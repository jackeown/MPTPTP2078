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

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 808 expanded)
%              Number of clauses        :   80 ( 198 expanded)
%              Number of leaves         :   22 ( 198 expanded)
%              Depth                    :   21
%              Number of atoms          :  359 (2711 expanded)
%              Number of equality atoms :  175 (1006 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
    ( ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
      | ~ v4_pre_topc(sK2,sK1) )
    & ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
      | v4_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f46,f48,f47])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f80])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f79])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
    inference(definition_unfolding,[],[f55,f80])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f60,f79,f80])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_790,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_797,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_798,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5473,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_797,c_798])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_145,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k5_xboole_0(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) = k4_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_146])).

cnf(c_787,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_879,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_787,c_11])).

cnf(c_9379,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_879])).

cnf(c_25111,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,X0)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5473,c_9379])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25627,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,X0)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25111,c_27])).

cnf(c_25628,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,X0)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_25627])).

cnf(c_25637,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_790,c_25628])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_794,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2959,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_794])).

cnf(c_1038,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3463,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2959,c_24,c_23,c_1038])).

cnf(c_22,negated_conjecture,
    ( v4_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_791,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_793,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1861,plain,
    ( v4_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_793])).

cnf(c_2216,plain,
    ( r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1861,c_27])).

cnf(c_2217,plain,
    ( v4_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2216])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_801,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3294,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_801])).

cnf(c_4110,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_791,c_3294])).

cnf(c_3092,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_798])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_191,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_146])).

cnf(c_786,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_3456,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(superposition,[status(thm)],[c_3092,c_786])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_800,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3857,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3456,c_800])).

cnf(c_4241,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2)
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4110,c_3857])).

cnf(c_4609,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4241,c_801])).

cnf(c_4615,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k2_tops_1(sK1,sK2),k2_tops_1(sK1,sK2))) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_4609,c_11])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_817,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_6])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1288,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_4])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_846,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_11])).

cnf(c_2003,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1288,c_846])).

cnf(c_3,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2022,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2003,c_3])).

cnf(c_4626,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = sK2 ),
    inference(demodulation,[status(thm)],[c_4615,c_817,c_2022])).

cnf(c_25639,plain,
    ( k2_pre_topc(sK1,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_25637,c_3463,c_4626])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_795,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4307,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_795])).

cnf(c_1042,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4603,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4307,c_24,c_23,c_1042])).

cnf(c_25659,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_25639,c_4603])).

cnf(c_17,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_796,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5200,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_796])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1006,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1007,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_5738,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5200,c_26,c_27,c_28,c_1007])).

cnf(c_25658,plain,
    ( v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_25639,c_5738])).

cnf(c_21,negated_conjecture,
    ( ~ v4_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25659,c_25658,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:36:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.97/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.97/1.49  
% 7.97/1.49  ------  iProver source info
% 7.97/1.49  
% 7.97/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.97/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.97/1.49  git: non_committed_changes: false
% 7.97/1.49  git: last_make_outside_of_git: false
% 7.97/1.49  
% 7.97/1.49  ------ 
% 7.97/1.49  ------ Parsing...
% 7.97/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.97/1.49  ------ Proving...
% 7.97/1.49  ------ Problem Properties 
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  clauses                                 26
% 7.97/1.49  conjectures                             5
% 7.97/1.49  EPR                                     3
% 7.97/1.49  Horn                                    24
% 7.97/1.49  unary                                   11
% 7.97/1.49  binary                                  8
% 7.97/1.49  lits                                    50
% 7.97/1.49  lits eq                                 14
% 7.97/1.49  fd_pure                                 0
% 7.97/1.49  fd_pseudo                               0
% 7.97/1.49  fd_cond                                 0
% 7.97/1.49  fd_pseudo_cond                          0
% 7.97/1.49  AC symbols                              0
% 7.97/1.49  
% 7.97/1.49  ------ Input Options Time Limit: Unbounded
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  ------ 
% 7.97/1.49  Current options:
% 7.97/1.49  ------ 
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  ------ Proving...
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  % SZS status Theorem for theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  fof(f22,conjecture,(
% 7.97/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f23,negated_conjecture,(
% 7.97/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.97/1.49    inference(negated_conjecture,[],[f22])).
% 7.97/1.49  
% 7.97/1.49  fof(f38,plain,(
% 7.97/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.97/1.49    inference(ennf_transformation,[],[f23])).
% 7.97/1.49  
% 7.97/1.49  fof(f39,plain,(
% 7.97/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.97/1.49    inference(flattening,[],[f38])).
% 7.97/1.49  
% 7.97/1.49  fof(f45,plain,(
% 7.97/1.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.97/1.49    inference(nnf_transformation,[],[f39])).
% 7.97/1.49  
% 7.97/1.49  fof(f46,plain,(
% 7.97/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.97/1.49    inference(flattening,[],[f45])).
% 7.97/1.49  
% 7.97/1.49  fof(f48,plain,(
% 7.97/1.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) != k2_tops_1(X0,sK2) | ~v4_pre_topc(sK2,X0)) & (k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) = k2_tops_1(X0,sK2) | v4_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.97/1.49    introduced(choice_axiom,[])).
% 7.97/1.49  
% 7.97/1.49  fof(f47,plain,(
% 7.97/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) != k2_tops_1(sK1,X1) | ~v4_pre_topc(X1,sK1)) & (k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) = k2_tops_1(sK1,X1) | v4_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 7.97/1.49    introduced(choice_axiom,[])).
% 7.97/1.49  
% 7.97/1.49  fof(f49,plain,(
% 7.97/1.49    ((k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) | ~v4_pre_topc(sK2,sK1)) & (k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) | v4_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 7.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f46,f48,f47])).
% 7.97/1.49  
% 7.97/1.49  fof(f76,plain,(
% 7.97/1.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.97/1.49    inference(cnf_transformation,[],[f49])).
% 7.97/1.49  
% 7.97/1.49  fof(f17,axiom,(
% 7.97/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f30,plain,(
% 7.97/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.97/1.49    inference(ennf_transformation,[],[f17])).
% 7.97/1.49  
% 7.97/1.49  fof(f31,plain,(
% 7.97/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.97/1.49    inference(flattening,[],[f30])).
% 7.97/1.49  
% 7.97/1.49  fof(f69,plain,(
% 7.97/1.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f31])).
% 7.97/1.49  
% 7.97/1.49  fof(f16,axiom,(
% 7.97/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f44,plain,(
% 7.97/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.97/1.49    inference(nnf_transformation,[],[f16])).
% 7.97/1.49  
% 7.97/1.49  fof(f67,plain,(
% 7.97/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f44])).
% 7.97/1.49  
% 7.97/1.49  fof(f13,axiom,(
% 7.97/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f27,plain,(
% 7.97/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.97/1.49    inference(ennf_transformation,[],[f13])).
% 7.97/1.49  
% 7.97/1.49  fof(f28,plain,(
% 7.97/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.97/1.49    inference(flattening,[],[f27])).
% 7.97/1.49  
% 7.97/1.49  fof(f64,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f28])).
% 7.97/1.49  
% 7.97/1.49  fof(f10,axiom,(
% 7.97/1.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f61,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f10])).
% 7.97/1.49  
% 7.97/1.49  fof(f3,axiom,(
% 7.97/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f54,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f3])).
% 7.97/1.49  
% 7.97/1.49  fof(f15,axiom,(
% 7.97/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f66,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f15])).
% 7.97/1.49  
% 7.97/1.49  fof(f79,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.97/1.49    inference(definition_unfolding,[],[f54,f66])).
% 7.97/1.49  
% 7.97/1.49  fof(f80,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f61,f79])).
% 7.97/1.49  
% 7.97/1.49  fof(f89,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.49    inference(definition_unfolding,[],[f64,f80])).
% 7.97/1.49  
% 7.97/1.49  fof(f68,plain,(
% 7.97/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f44])).
% 7.97/1.49  
% 7.97/1.49  fof(f12,axiom,(
% 7.97/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f63,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f12])).
% 7.97/1.49  
% 7.97/1.49  fof(f88,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.97/1.49    inference(definition_unfolding,[],[f63,f80])).
% 7.97/1.49  
% 7.97/1.49  fof(f75,plain,(
% 7.97/1.49    l1_pre_topc(sK1)),
% 7.97/1.49    inference(cnf_transformation,[],[f49])).
% 7.97/1.49  
% 7.97/1.49  fof(f20,axiom,(
% 7.97/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f35,plain,(
% 7.97/1.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.49    inference(ennf_transformation,[],[f20])).
% 7.97/1.49  
% 7.97/1.49  fof(f72,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f35])).
% 7.97/1.49  
% 7.97/1.49  fof(f77,plain,(
% 7.97/1.49    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) | v4_pre_topc(sK2,sK1)),
% 7.97/1.49    inference(cnf_transformation,[],[f49])).
% 7.97/1.49  
% 7.97/1.49  fof(f21,axiom,(
% 7.97/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f36,plain,(
% 7.97/1.49    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.49    inference(ennf_transformation,[],[f21])).
% 7.97/1.49  
% 7.97/1.49  fof(f37,plain,(
% 7.97/1.49    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.49    inference(flattening,[],[f36])).
% 7.97/1.49  
% 7.97/1.49  fof(f73,plain,(
% 7.97/1.49    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f37])).
% 7.97/1.49  
% 7.97/1.49  fof(f5,axiom,(
% 7.97/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f26,plain,(
% 7.97/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.97/1.49    inference(ennf_transformation,[],[f5])).
% 7.97/1.49  
% 7.97/1.49  fof(f56,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f26])).
% 7.97/1.49  
% 7.97/1.49  fof(f83,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f56,f66])).
% 7.97/1.49  
% 7.97/1.49  fof(f14,axiom,(
% 7.97/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f29,plain,(
% 7.97/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.97/1.49    inference(ennf_transformation,[],[f14])).
% 7.97/1.49  
% 7.97/1.49  fof(f65,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f29])).
% 7.97/1.49  
% 7.97/1.49  fof(f90,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.49    inference(definition_unfolding,[],[f65,f79])).
% 7.97/1.49  
% 7.97/1.49  fof(f7,axiom,(
% 7.97/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f58,plain,(
% 7.97/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f7])).
% 7.97/1.49  
% 7.97/1.49  fof(f85,plain,(
% 7.97/1.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f58,f79])).
% 7.97/1.49  
% 7.97/1.49  fof(f8,axiom,(
% 7.97/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f59,plain,(
% 7.97/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.97/1.49    inference(cnf_transformation,[],[f8])).
% 7.97/1.49  
% 7.97/1.49  fof(f86,plain,(
% 7.97/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 7.97/1.49    inference(definition_unfolding,[],[f59,f79])).
% 7.97/1.49  
% 7.97/1.49  fof(f6,axiom,(
% 7.97/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f57,plain,(
% 7.97/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.97/1.49    inference(cnf_transformation,[],[f6])).
% 7.97/1.49  
% 7.97/1.49  fof(f84,plain,(
% 7.97/1.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 7.97/1.49    inference(definition_unfolding,[],[f57,f66])).
% 7.97/1.49  
% 7.97/1.49  fof(f4,axiom,(
% 7.97/1.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f55,plain,(
% 7.97/1.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.97/1.49    inference(cnf_transformation,[],[f4])).
% 7.97/1.49  
% 7.97/1.49  fof(f82,plain,(
% 7.97/1.49    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0) )),
% 7.97/1.49    inference(definition_unfolding,[],[f55,f80])).
% 7.97/1.49  
% 7.97/1.49  fof(f9,axiom,(
% 7.97/1.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f60,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.97/1.49    inference(cnf_transformation,[],[f9])).
% 7.97/1.49  
% 7.97/1.49  fof(f87,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0) )),
% 7.97/1.49    inference(definition_unfolding,[],[f60,f79,f80])).
% 7.97/1.49  
% 7.97/1.49  fof(f2,axiom,(
% 7.97/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f24,plain,(
% 7.97/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.97/1.49    inference(rectify,[],[f2])).
% 7.97/1.49  
% 7.97/1.49  fof(f53,plain,(
% 7.97/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.97/1.49    inference(cnf_transformation,[],[f24])).
% 7.97/1.49  
% 7.97/1.49  fof(f81,plain,(
% 7.97/1.49    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 7.97/1.49    inference(definition_unfolding,[],[f53,f66])).
% 7.97/1.49  
% 7.97/1.49  fof(f19,axiom,(
% 7.97/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f34,plain,(
% 7.97/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.49    inference(ennf_transformation,[],[f19])).
% 7.97/1.49  
% 7.97/1.49  fof(f71,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f34])).
% 7.97/1.49  
% 7.97/1.49  fof(f18,axiom,(
% 7.97/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 7.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f32,plain,(
% 7.97/1.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.97/1.49    inference(ennf_transformation,[],[f18])).
% 7.97/1.49  
% 7.97/1.49  fof(f33,plain,(
% 7.97/1.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.97/1.49    inference(flattening,[],[f32])).
% 7.97/1.49  
% 7.97/1.49  fof(f70,plain,(
% 7.97/1.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f33])).
% 7.97/1.49  
% 7.97/1.49  fof(f74,plain,(
% 7.97/1.49    v2_pre_topc(sK1)),
% 7.97/1.49    inference(cnf_transformation,[],[f49])).
% 7.97/1.49  
% 7.97/1.49  fof(f78,plain,(
% 7.97/1.49    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) | ~v4_pre_topc(sK2,sK1)),
% 7.97/1.49    inference(cnf_transformation,[],[f49])).
% 7.97/1.49  
% 7.97/1.49  cnf(c_23,negated_conjecture,
% 7.97/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.97/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_790,plain,
% 7.97/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_16,plain,
% 7.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.49      | ~ l1_pre_topc(X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_797,plain,
% 7.97/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.97/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.97/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_15,plain,
% 7.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_798,plain,
% 7.97/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.97/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5473,plain,
% 7.97/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.97/1.49      | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
% 7.97/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_797,c_798]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_12,plain,
% 7.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.97/1.49      | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
% 7.97/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_14,plain,
% 7.97/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_145,plain,
% 7.97/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.97/1.49      inference(prop_impl,[status(thm)],[c_14]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_146,plain,
% 7.97/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.97/1.49      inference(renaming,[status(thm)],[c_145]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_190,plain,
% 7.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.49      | ~ r1_tarski(X2,X1)
% 7.97/1.49      | k5_xboole_0(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) = k4_subset_1(X1,X0,X2) ),
% 7.97/1.49      inference(bin_hyper_res,[status(thm)],[c_12,c_146]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_787,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
% 7.97/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.97/1.49      | r1_tarski(X1,X2) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_11,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 7.97/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_879,plain,
% 7.97/1.49      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 7.97/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.97/1.49      | r1_tarski(X2,X0) != iProver_top ),
% 7.97/1.49      inference(light_normalisation,[status(thm)],[c_787,c_11]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_9379,plain,
% 7.97/1.49      ( k4_subset_1(u1_struct_0(sK1),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
% 7.97/1.49      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_790,c_879]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_25111,plain,
% 7.97/1.49      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,X0)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,X0)))
% 7.97/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.97/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_5473,c_9379]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_24,negated_conjecture,
% 7.97/1.49      ( l1_pre_topc(sK1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_27,plain,
% 7.97/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_25627,plain,
% 7.97/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.97/1.49      | k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,X0)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,X0))) ),
% 7.97/1.49      inference(global_propositional_subsumption,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_25111,c_27]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_25628,plain,
% 7.97/1.49      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,X0)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,X0)))
% 7.97/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.97/1.49      inference(renaming,[status(thm)],[c_25627]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_25637,plain,
% 7.97/1.49      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_790,c_25628]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_19,plain,
% 7.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.49      | ~ l1_pre_topc(X1)
% 7.97/1.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.97/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_794,plain,
% 7.97/1.49      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.97/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.97/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_2959,plain,
% 7.97/1.49      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2)
% 7.97/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_790,c_794]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1038,plain,
% 7.97/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.97/1.49      | ~ l1_pre_topc(sK1)
% 7.97/1.49      | k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3463,plain,
% 7.97/1.49      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
% 7.97/1.49      inference(global_propositional_subsumption,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_2959,c_24,c_23,c_1038]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_22,negated_conjecture,
% 7.97/1.49      ( v4_pre_topc(sK2,sK1)
% 7.97/1.49      | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 7.97/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_791,plain,
% 7.97/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 7.97/1.49      | v4_pre_topc(sK2,sK1) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_20,plain,
% 7.97/1.49      ( ~ v4_pre_topc(X0,X1)
% 7.97/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.49      | r1_tarski(k2_tops_1(X1,X0),X0)
% 7.97/1.49      | ~ l1_pre_topc(X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_793,plain,
% 7.97/1.49      ( v4_pre_topc(X0,X1) != iProver_top
% 7.97/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.97/1.49      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 7.97/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1861,plain,
% 7.97/1.49      ( v4_pre_topc(sK2,sK1) != iProver_top
% 7.97/1.49      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
% 7.97/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_790,c_793]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_2216,plain,
% 7.97/1.49      ( r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
% 7.97/1.49      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 7.97/1.49      inference(global_propositional_subsumption,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_1861,c_27]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_2217,plain,
% 7.97/1.49      ( v4_pre_topc(sK2,sK1) != iProver_top
% 7.97/1.49      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
% 7.97/1.49      inference(renaming,[status(thm)],[c_2216]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5,plain,
% 7.97/1.49      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 7.97/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_801,plain,
% 7.97/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 7.97/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3294,plain,
% 7.97/1.49      ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2)
% 7.97/1.49      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_2217,c_801]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4110,plain,
% 7.97/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 7.97/1.49      | k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2) ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_791,c_3294]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3092,plain,
% 7.97/1.49      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_790,c_798]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_13,plain,
% 7.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 7.97/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_191,plain,
% 7.97/1.49      ( ~ r1_tarski(X0,X1)
% 7.97/1.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 7.97/1.49      inference(bin_hyper_res,[status(thm)],[c_13,c_146]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_786,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 7.97/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3456,plain,
% 7.97/1.49      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_3092,c_786]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_7,plain,
% 7.97/1.49      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 7.97/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_800,plain,
% 7.97/1.49      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3857,plain,
% 7.97/1.49      ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,X0),sK2) = iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_3456,c_800]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4241,plain,
% 7.97/1.49      ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2)
% 7.97/1.49      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_4110,c_3857]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4609,plain,
% 7.97/1.49      ( k1_setfam_1(k2_tarski(k2_tops_1(sK1,sK2),sK2)) = k2_tops_1(sK1,sK2) ),
% 7.97/1.49      inference(forward_subsumption_resolution,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_4241,c_801]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4615,plain,
% 7.97/1.49      ( k5_xboole_0(sK2,k5_xboole_0(k2_tops_1(sK1,sK2),k2_tops_1(sK1,sK2))) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_4609,c_11]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_8,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 7.97/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_6,plain,
% 7.97/1.49      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.97/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_817,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.97/1.49      inference(light_normalisation,[status(thm)],[c_8,c_6]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
% 7.97/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1288,plain,
% 7.97/1.49      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_11,c_4]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_9,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
% 7.97/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_846,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
% 7.97/1.49      inference(light_normalisation,[status(thm)],[c_9,c_11]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_2003,plain,
% 7.97/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k1_xboole_0 ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_1288,c_846]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3,plain,
% 7.97/1.49      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 7.97/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_2022,plain,
% 7.97/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.97/1.49      inference(light_normalisation,[status(thm)],[c_2003,c_3]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4626,plain,
% 7.97/1.49      ( k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = sK2 ),
% 7.97/1.49      inference(demodulation,[status(thm)],[c_4615,c_817,c_2022]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_25639,plain,
% 7.97/1.49      ( k2_pre_topc(sK1,sK2) = sK2 ),
% 7.97/1.49      inference(light_normalisation,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_25637,c_3463,c_4626]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_18,plain,
% 7.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.49      | ~ l1_pre_topc(X1)
% 7.97/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.97/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_795,plain,
% 7.97/1.49      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.97/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.97/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4307,plain,
% 7.97/1.49      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 7.97/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_790,c_795]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1042,plain,
% 7.97/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.97/1.49      | ~ l1_pre_topc(sK1)
% 7.97/1.49      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_4603,plain,
% 7.97/1.49      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 7.97/1.49      inference(global_propositional_subsumption,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_4307,c_24,c_23,c_1042]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_25659,plain,
% 7.97/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 7.97/1.49      inference(demodulation,[status(thm)],[c_25639,c_4603]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_17,plain,
% 7.97/1.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 7.97/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.97/1.49      | ~ v2_pre_topc(X0)
% 7.97/1.49      | ~ l1_pre_topc(X0) ),
% 7.97/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_796,plain,
% 7.97/1.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 7.97/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.97/1.49      | v2_pre_topc(X0) != iProver_top
% 7.97/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5200,plain,
% 7.97/1.49      ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top
% 7.97/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.97/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_790,c_796]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_25,negated_conjecture,
% 7.97/1.49      ( v2_pre_topc(sK1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_26,plain,
% 7.97/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_28,plain,
% 7.97/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1006,plain,
% 7.97/1.49      ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1)
% 7.97/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.97/1.49      | ~ v2_pre_topc(sK1)
% 7.97/1.49      | ~ l1_pre_topc(sK1) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1007,plain,
% 7.97/1.49      ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top
% 7.97/1.49      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.97/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.97/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_1006]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5738,plain,
% 7.97/1.49      ( v4_pre_topc(k2_pre_topc(sK1,sK2),sK1) = iProver_top ),
% 7.97/1.49      inference(global_propositional_subsumption,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_5200,c_26,c_27,c_28,c_1007]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_25658,plain,
% 7.97/1.49      ( v4_pre_topc(sK2,sK1) = iProver_top ),
% 7.97/1.49      inference(demodulation,[status(thm)],[c_25639,c_5738]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_21,negated_conjecture,
% 7.97/1.49      ( ~ v4_pre_topc(sK2,sK1)
% 7.97/1.49      | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) ),
% 7.97/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_30,plain,
% 7.97/1.49      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
% 7.97/1.49      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(contradiction,plain,
% 7.97/1.49      ( $false ),
% 7.97/1.49      inference(minisat,[status(thm)],[c_25659,c_25658,c_30]) ).
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  ------                               Statistics
% 7.97/1.49  
% 7.97/1.49  ------ Selected
% 7.97/1.49  
% 7.97/1.49  total_time:                             0.771
% 7.97/1.49  
%------------------------------------------------------------------------------
