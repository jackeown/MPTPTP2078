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
% DateTime   : Thu Dec  3 12:14:28 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 862 expanded)
%              Number of clauses        :   78 ( 196 expanded)
%              Number of leaves         :   22 ( 214 expanded)
%              Depth                    :   21
%              Number of atoms          :  355 (3097 expanded)
%              Number of equality atoms :  179 (1128 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) != k2_tops_1(X0,sK2)
          | ~ v4_pre_topc(sK2,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) = k2_tops_1(X0,sK2)
          | v4_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
          ( ( k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) != k2_tops_1(sK1,X1)
            | ~ v4_pre_topc(X1,sK1) )
          & ( k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) = k2_tops_1(sK1,X1)
            | v4_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
      | ~ v4_pre_topc(sK2,sK1) )
    & ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
      | v4_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f54,f56,f55])).

fof(f88,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f90])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f66,f90])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f69,f90])).

fof(f99,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f71,f91])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f67,f90])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f65,f78])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
    inference(definition_unfolding,[],[f63,f91])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f68,f90,f91])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f61,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f78])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f76,f91])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( v4_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_847,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_846,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_849,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1222,plain,
    ( v4_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_849])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1556,plain,
    ( r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1222,c_30])).

cnf(c_1557,plain,
    ( v4_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_1556])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_862,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4085,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_862])).

cnf(c_4102,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_847,c_4085])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_855,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5075,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(superposition,[status(thm)],[c_846,c_855])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_861,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5337,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5075,c_861])).

cnf(c_5593,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2)
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4102,c_5337])).

cnf(c_7221,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5593,c_862])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_7227,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_tops_1(sK1,sK2),k2_tops_1(sK1,sK2))) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_7221,c_11])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_878,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_6])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1363,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_4])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_903,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_11])).

cnf(c_2419,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1363,c_903])).

cnf(c_3,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2438,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2419,c_3])).

cnf(c_7232,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = sK2 ),
    inference(demodulation,[status(thm)],[c_7227,c_878,c_2438])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_851,plain,
    ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3342,plain,
    ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_851])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3951,plain,
    ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3342,c_27,c_26,c_1139])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_854,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7631,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3951,c_854])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1086,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1087,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_8153,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7631,c_30,c_31,c_1087])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_856,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_978,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_856,c_11])).

cnf(c_9637,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_978])).

cnf(c_9919,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_8153,c_9637])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_850,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2207,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_850])).

cnf(c_1167,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2640,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2207,c_27,c_26,c_1167])).

cnf(c_9921,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k2_pre_topc(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_9919,c_2640])).

cnf(c_10911,plain,
    ( k2_pre_topc(sK1,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_7232,c_9921])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_852,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4500,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_852])).

cnf(c_1170,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_5588,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4500,c_27,c_26,c_1170])).

cnf(c_11212,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_10911,c_5588])).

cnf(c_19,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_853,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6664,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_853])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_29,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1131,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1132,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_7213,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6664,c_29,c_30,c_31,c_1132])).

cnf(c_11211,plain,
    ( v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10911,c_7213])).

cnf(c_24,negated_conjecture,
    ( ~ v4_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11212,c_11211,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:08:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.49/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/1.01  
% 3.49/1.01  ------  iProver source info
% 3.49/1.01  
% 3.49/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.49/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/1.01  git: non_committed_changes: false
% 3.49/1.01  git: last_make_outside_of_git: false
% 3.49/1.01  
% 3.49/1.01  ------ 
% 3.49/1.01  ------ Parsing...
% 3.49/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/1.01  ------ Proving...
% 3.49/1.01  ------ Problem Properties 
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  clauses                                 29
% 3.49/1.01  conjectures                             5
% 3.49/1.01  EPR                                     3
% 3.49/1.01  Horn                                    27
% 3.49/1.01  unary                                   11
% 3.49/1.01  binary                                  9
% 3.49/1.01  lits                                    58
% 3.49/1.01  lits eq                                 17
% 3.49/1.01  fd_pure                                 0
% 3.49/1.01  fd_pseudo                               0
% 3.49/1.01  fd_cond                                 0
% 3.49/1.01  fd_pseudo_cond                          0
% 3.49/1.01  AC symbols                              0
% 3.49/1.01  
% 3.49/1.01  ------ Input Options Time Limit: Unbounded
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  ------ 
% 3.49/1.01  Current options:
% 3.49/1.01  ------ 
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  ------ Proving...
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  % SZS status Theorem for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  fof(f26,conjecture,(
% 3.49/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f27,negated_conjecture,(
% 3.49/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.49/1.01    inference(negated_conjecture,[],[f26])).
% 3.49/1.01  
% 3.49/1.01  fof(f47,plain,(
% 3.49/1.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.49/1.01    inference(ennf_transformation,[],[f27])).
% 3.49/1.01  
% 3.49/1.01  fof(f48,plain,(
% 3.49/1.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.49/1.01    inference(flattening,[],[f47])).
% 3.49/1.01  
% 3.49/1.01  fof(f53,plain,(
% 3.49/1.01    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.49/1.01    inference(nnf_transformation,[],[f48])).
% 3.49/1.01  
% 3.49/1.01  fof(f54,plain,(
% 3.49/1.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.49/1.01    inference(flattening,[],[f53])).
% 3.49/1.01  
% 3.49/1.01  fof(f56,plain,(
% 3.49/1.01    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) != k2_tops_1(X0,sK2) | ~v4_pre_topc(sK2,X0)) & (k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) = k2_tops_1(X0,sK2) | v4_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f55,plain,(
% 3.49/1.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) != k2_tops_1(sK1,X1) | ~v4_pre_topc(X1,sK1)) & (k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) = k2_tops_1(sK1,X1) | v4_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f57,plain,(
% 3.49/1.01    ((k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) | ~v4_pre_topc(sK2,sK1)) & (k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) | v4_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f54,f56,f55])).
% 3.49/1.01  
% 3.49/1.01  fof(f88,plain,(
% 3.49/1.01    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) | v4_pre_topc(sK2,sK1)),
% 3.49/1.01    inference(cnf_transformation,[],[f57])).
% 3.49/1.01  
% 3.49/1.01  fof(f87,plain,(
% 3.49/1.01    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.49/1.01    inference(cnf_transformation,[],[f57])).
% 3.49/1.01  
% 3.49/1.01  fof(f25,axiom,(
% 3.49/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f45,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.49/1.01    inference(ennf_transformation,[],[f25])).
% 3.49/1.01  
% 3.49/1.01  fof(f46,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.49/1.01    inference(flattening,[],[f45])).
% 3.49/1.01  
% 3.49/1.01  fof(f84,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f46])).
% 3.49/1.01  
% 3.49/1.01  fof(f86,plain,(
% 3.49/1.01    l1_pre_topc(sK1)),
% 3.49/1.01    inference(cnf_transformation,[],[f57])).
% 3.49/1.01  
% 3.49/1.01  fof(f5,axiom,(
% 3.49/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f30,plain,(
% 3.49/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.49/1.01    inference(ennf_transformation,[],[f5])).
% 3.49/1.01  
% 3.49/1.01  fof(f64,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f30])).
% 3.49/1.01  
% 3.49/1.01  fof(f19,axiom,(
% 3.49/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f78,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f19])).
% 3.49/1.01  
% 3.49/1.01  fof(f94,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f64,f78])).
% 3.49/1.01  
% 3.49/1.01  fof(f18,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f37,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.49/1.01    inference(ennf_transformation,[],[f18])).
% 3.49/1.01  
% 3.49/1.01  fof(f77,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f37])).
% 3.49/1.01  
% 3.49/1.01  fof(f3,axiom,(
% 3.49/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f62,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f3])).
% 3.49/1.01  
% 3.49/1.01  fof(f90,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f62,f78])).
% 3.49/1.01  
% 3.49/1.01  fof(f102,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f77,f90])).
% 3.49/1.01  
% 3.49/1.01  fof(f7,axiom,(
% 3.49/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f66,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f7])).
% 3.49/1.01  
% 3.49/1.01  fof(f96,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f66,f90])).
% 3.49/1.01  
% 3.49/1.01  fof(f12,axiom,(
% 3.49/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f71,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f12])).
% 3.49/1.01  
% 3.49/1.01  fof(f10,axiom,(
% 3.49/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f69,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f10])).
% 3.49/1.01  
% 3.49/1.01  fof(f91,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f69,f90])).
% 3.49/1.01  
% 3.49/1.01  fof(f99,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f71,f91])).
% 3.49/1.01  
% 3.49/1.01  fof(f8,axiom,(
% 3.49/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f67,plain,(
% 3.49/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.49/1.01    inference(cnf_transformation,[],[f8])).
% 3.49/1.01  
% 3.49/1.01  fof(f97,plain,(
% 3.49/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 3.49/1.01    inference(definition_unfolding,[],[f67,f90])).
% 3.49/1.01  
% 3.49/1.01  fof(f6,axiom,(
% 3.49/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f65,plain,(
% 3.49/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.49/1.01    inference(cnf_transformation,[],[f6])).
% 3.49/1.01  
% 3.49/1.01  fof(f95,plain,(
% 3.49/1.01    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f65,f78])).
% 3.49/1.01  
% 3.49/1.01  fof(f4,axiom,(
% 3.49/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f63,plain,(
% 3.49/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.49/1.01    inference(cnf_transformation,[],[f4])).
% 3.49/1.01  
% 3.49/1.01  fof(f93,plain,(
% 3.49/1.01    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0) )),
% 3.49/1.01    inference(definition_unfolding,[],[f63,f91])).
% 3.49/1.01  
% 3.49/1.01  fof(f9,axiom,(
% 3.49/1.01    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f68,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.49/1.01    inference(cnf_transformation,[],[f9])).
% 3.49/1.01  
% 3.49/1.01  fof(f98,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0) )),
% 3.49/1.01    inference(definition_unfolding,[],[f68,f90,f91])).
% 3.49/1.01  
% 3.49/1.01  fof(f2,axiom,(
% 3.49/1.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f28,plain,(
% 3.49/1.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.49/1.01    inference(rectify,[],[f2])).
% 3.49/1.01  
% 3.49/1.01  fof(f61,plain,(
% 3.49/1.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.49/1.01    inference(cnf_transformation,[],[f28])).
% 3.49/1.01  
% 3.49/1.01  fof(f92,plain,(
% 3.49/1.01    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 3.49/1.01    inference(definition_unfolding,[],[f61,f78])).
% 3.49/1.01  
% 3.49/1.01  fof(f23,axiom,(
% 3.49/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f43,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.49/1.01    inference(ennf_transformation,[],[f23])).
% 3.49/1.01  
% 3.49/1.01  fof(f82,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f43])).
% 3.49/1.01  
% 3.49/1.01  fof(f20,axiom,(
% 3.49/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f38,plain,(
% 3.49/1.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.49/1.01    inference(ennf_transformation,[],[f20])).
% 3.49/1.01  
% 3.49/1.01  fof(f39,plain,(
% 3.49/1.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.49/1.01    inference(flattening,[],[f38])).
% 3.49/1.01  
% 3.49/1.01  fof(f79,plain,(
% 3.49/1.01    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f39])).
% 3.49/1.01  
% 3.49/1.01  fof(f17,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f35,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.49/1.01    inference(ennf_transformation,[],[f17])).
% 3.49/1.01  
% 3.49/1.01  fof(f36,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.49/1.01    inference(flattening,[],[f35])).
% 3.49/1.01  
% 3.49/1.01  fof(f76,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f36])).
% 3.49/1.01  
% 3.49/1.01  fof(f101,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f76,f91])).
% 3.49/1.01  
% 3.49/1.01  fof(f24,axiom,(
% 3.49/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f44,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.49/1.01    inference(ennf_transformation,[],[f24])).
% 3.49/1.01  
% 3.49/1.01  fof(f83,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f44])).
% 3.49/1.01  
% 3.49/1.01  fof(f22,axiom,(
% 3.49/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f42,plain,(
% 3.49/1.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.49/1.01    inference(ennf_transformation,[],[f22])).
% 3.49/1.01  
% 3.49/1.01  fof(f81,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f42])).
% 3.49/1.01  
% 3.49/1.01  fof(f21,axiom,(
% 3.49/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f40,plain,(
% 3.49/1.01    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.49/1.01    inference(ennf_transformation,[],[f21])).
% 3.49/1.01  
% 3.49/1.01  fof(f41,plain,(
% 3.49/1.01    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.49/1.01    inference(flattening,[],[f40])).
% 3.49/1.01  
% 3.49/1.01  fof(f80,plain,(
% 3.49/1.01    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f41])).
% 3.49/1.01  
% 3.49/1.01  fof(f85,plain,(
% 3.49/1.01    v2_pre_topc(sK1)),
% 3.49/1.01    inference(cnf_transformation,[],[f57])).
% 3.49/1.01  
% 3.49/1.01  fof(f89,plain,(
% 3.49/1.01    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) | ~v4_pre_topc(sK2,sK1)),
% 3.49/1.01    inference(cnf_transformation,[],[f57])).
% 3.49/1.01  
% 3.49/1.01  cnf(c_25,negated_conjecture,
% 3.49/1.01      ( v4_pre_topc(sK2,sK1)
% 3.49/1.01      | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_847,plain,
% 3.49/1.01      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 3.49/1.01      | v4_pre_topc(sK2,sK1) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_26,negated_conjecture,
% 3.49/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.49/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_846,plain,
% 3.49/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_23,plain,
% 3.49/1.01      ( ~ v4_pre_topc(X0,X1)
% 3.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.49/1.01      | r1_tarski(k2_tops_1(X1,X0),X0)
% 3.49/1.01      | ~ l1_pre_topc(X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_849,plain,
% 3.49/1.01      ( v4_pre_topc(X0,X1) != iProver_top
% 3.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.49/1.01      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.49/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1222,plain,
% 3.49/1.01      ( v4_pre_topc(sK2,sK1) != iProver_top
% 3.49/1.01      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
% 3.49/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_846,c_849]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_27,negated_conjecture,
% 3.49/1.01      ( l1_pre_topc(sK1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_30,plain,
% 3.49/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1556,plain,
% 3.49/1.01      ( r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
% 3.49/1.01      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_1222,c_30]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1557,plain,
% 3.49/1.01      ( v4_pre_topc(sK2,sK1) != iProver_top
% 3.49/1.01      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
% 3.49/1.01      inference(renaming,[status(thm)],[c_1556]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5,plain,
% 3.49/1.01      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_862,plain,
% 3.49/1.01      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 3.49/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4085,plain,
% 3.49/1.01      ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2)
% 3.49/1.01      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_1557,c_862]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4102,plain,
% 3.49/1.01      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 3.49/1.01      | k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_847,c_4085]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_17,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/1.01      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.49/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_855,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5075,plain,
% 3.49/1.01      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_846,c_855]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_7,plain,
% 3.49/1.01      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_861,plain,
% 3.49/1.01      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5337,plain,
% 3.49/1.01      ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,X0),sK2) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_5075,c_861]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5593,plain,
% 3.49/1.01      ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2)
% 3.49/1.01      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_4102,c_5337]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_7221,plain,
% 3.49/1.01      ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(forward_subsumption_resolution,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_5593,c_862]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_7227,plain,
% 3.49/1.01      ( k5_xboole_0(sK2,k5_xboole_0(k2_tops_1(sK1,sK2),k2_tops_1(sK1,sK2))) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_7221,c_11]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_8,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6,plain,
% 3.49/1.01      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_878,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.49/1.01      inference(light_normalisation,[status(thm)],[c_8,c_6]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1363,plain,
% 3.49/1.01      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_11,c_4]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_903,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
% 3.49/1.01      inference(light_normalisation,[status(thm)],[c_9,c_11]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2419,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k1_xboole_0 ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_1363,c_903]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3,plain,
% 3.49/1.01      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2438,plain,
% 3.49/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.49/1.01      inference(light_normalisation,[status(thm)],[c_2419,c_3]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_7232,plain,
% 3.49/1.01      ( k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = sK2 ),
% 3.49/1.01      inference(demodulation,[status(thm)],[c_7227,c_878,c_2438]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_21,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.49/1.01      | ~ l1_pre_topc(X1)
% 3.49/1.01      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_851,plain,
% 3.49/1.01      ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
% 3.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.49/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3342,plain,
% 3.49/1.01      ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2)
% 3.49/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_846,c_851]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1139,plain,
% 3.49/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.49/1.01      | ~ l1_pre_topc(sK1)
% 3.49/1.01      | k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3951,plain,
% 3.49/1.01      ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_3342,c_27,c_26,c_1139]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_18,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.49/1.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.49/1.01      | ~ l1_pre_topc(X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_854,plain,
% 3.49/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.49/1.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.49/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_7631,plain,
% 3.49/1.01      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.49/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.49/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_3951,c_854]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_31,plain,
% 3.49/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1086,plain,
% 3.49/1.01      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.49/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.49/1.01      | ~ l1_pre_topc(sK1) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1087,plain,
% 3.49/1.01      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.49/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.49/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1086]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_8153,plain,
% 3.49/1.01      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_7631,c_30,c_31,c_1087]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_16,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.49/1.01      | k5_xboole_0(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) = k4_subset_1(X1,X0,X2) ),
% 3.49/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_856,plain,
% 3.49/1.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
% 3.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_978,plain,
% 3.49/1.01      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.49/1.01      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.49/1.01      inference(light_normalisation,[status(thm)],[c_856,c_11]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9637,plain,
% 3.49/1.01      ( k4_subset_1(u1_struct_0(sK1),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
% 3.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_846,c_978]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9919,plain,
% 3.49/1.01      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_8153,c_9637]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_22,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.49/1.01      | ~ l1_pre_topc(X1)
% 3.49/1.01      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_850,plain,
% 3.49/1.01      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.49/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2207,plain,
% 3.49/1.01      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2)
% 3.49/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_846,c_850]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1167,plain,
% 3.49/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.49/1.01      | ~ l1_pre_topc(sK1)
% 3.49/1.01      | k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2640,plain,
% 3.49/1.01      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_2207,c_27,c_26,c_1167]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9921,plain,
% 3.49/1.01      ( k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k2_pre_topc(sK1,sK2) ),
% 3.49/1.01      inference(light_normalisation,[status(thm)],[c_9919,c_2640]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_10911,plain,
% 3.49/1.01      ( k2_pre_topc(sK1,sK2) = sK2 ),
% 3.49/1.01      inference(demodulation,[status(thm)],[c_7232,c_9921]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_20,plain,
% 3.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.49/1.01      | ~ l1_pre_topc(X1)
% 3.49/1.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_852,plain,
% 3.49/1.01      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.49/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4500,plain,
% 3.49/1.01      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 3.49/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_846,c_852]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1170,plain,
% 3.49/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.49/1.01      | ~ l1_pre_topc(sK1)
% 3.49/1.01      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5588,plain,
% 3.49/1.01      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_4500,c_27,c_26,c_1170]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11212,plain,
% 3.49/1.01      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(demodulation,[status(thm)],[c_10911,c_5588]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_19,plain,
% 3.49/1.01      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.49/1.01      | ~ v2_pre_topc(X0)
% 3.49/1.01      | ~ l1_pre_topc(X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_853,plain,
% 3.49/1.01      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 3.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.49/1.01      | v2_pre_topc(X0) != iProver_top
% 3.49/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6664,plain,
% 3.49/1.01      ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top
% 3.49/1.01      | v2_pre_topc(sK1) != iProver_top
% 3.49/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_846,c_853]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_28,negated_conjecture,
% 3.49/1.01      ( v2_pre_topc(sK1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_29,plain,
% 3.49/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1131,plain,
% 3.49/1.01      ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1)
% 3.49/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.49/1.01      | ~ v2_pre_topc(sK1)
% 3.49/1.01      | ~ l1_pre_topc(sK1) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1132,plain,
% 3.49/1.01      ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top
% 3.49/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.49/1.01      | v2_pre_topc(sK1) != iProver_top
% 3.49/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1131]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_7213,plain,
% 3.49/1.01      ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_6664,c_29,c_30,c_31,c_1132]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_11211,plain,
% 3.49/1.01      ( v4_pre_topc(sK2,sK1) = iProver_top ),
% 3.49/1.01      inference(demodulation,[status(thm)],[c_10911,c_7213]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_24,negated_conjecture,
% 3.49/1.01      ( ~ v4_pre_topc(sK2,sK1)
% 3.49/1.01      | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) ),
% 3.49/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_33,plain,
% 3.49/1.01      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
% 3.49/1.01      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(contradiction,plain,
% 3.49/1.01      ( $false ),
% 3.49/1.01      inference(minisat,[status(thm)],[c_11212,c_11211,c_33]) ).
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  ------                               Statistics
% 3.49/1.01  
% 3.49/1.01  ------ Selected
% 3.49/1.01  
% 3.49/1.01  total_time:                             0.348
% 3.49/1.01  
%------------------------------------------------------------------------------
