%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:35 EST 2020

% Result     : Theorem 39.33s
% Output     : CNFRefutation 39.33s
% Verified   : 
% Statistics : Number of formulae       :  156 (1060 expanded)
%              Number of clauses        :   81 ( 270 expanded)
%              Number of leaves         :   21 ( 262 expanded)
%              Depth                    :   21
%              Number of atoms          :  346 (3181 expanded)
%              Number of equality atoms :  187 (1344 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_662,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1755,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_662])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_663,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2226,plain,
    ( k1_setfam_1(k2_tarski(k5_xboole_0(X0,X0),X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1755,c_663])).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_661,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3314,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_661])).

cnf(c_15125,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0
    | r1_tarski(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2226,c_3314])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1208,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_15154,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0
    | r1_tarski(k5_xboole_0(X0,X0),k3_tarski(k2_tarski(X0,X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15125,c_1208])).

cnf(c_1758,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_662])).

cnf(c_15130,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2226,c_1758])).

cnf(c_15141,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X0,X0)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15130,c_1208])).

cnf(c_19022,plain,
    ( k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X0)),X0)) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_15141,c_663])).

cnf(c_23756,plain,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X0)))) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_19022])).

cnf(c_6,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_660,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_684,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8,c_660])).

cnf(c_2222,plain,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_684,c_663])).

cnf(c_23795,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_23756,c_2222])).

cnf(c_111297,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0
    | r1_tarski(k5_xboole_0(X0,X0),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15154,c_23795])).

cnf(c_111300,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_111297,c_1755])).

cnf(c_17,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_651,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_650,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_656,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6307,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_656])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6573,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6307,c_22])).

cnf(c_6574,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6573])).

cnf(c_6579,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_651,c_6574])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_658,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1929,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_650,c_658])).

cnf(c_2446,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1929,c_662])).

cnf(c_2590,plain,
    ( k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_2446,c_663])).

cnf(c_2921,plain,
    ( k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_7,c_2590])).

cnf(c_6814,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_6579,c_2921])).

cnf(c_7166,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6579,c_6814])).

cnf(c_1210,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_7998,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_7166,c_1210])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_653,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6148,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_653])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_655,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_659,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_734,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_659,c_8])).

cnf(c_4653,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_734])).

cnf(c_4675,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_4653])).

cnf(c_4961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4675,c_22])).

cnf(c_4962,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4961])).

cnf(c_4970,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_650,c_4962])).

cnf(c_6151,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6148,c_4970])).

cnf(c_6860,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6151,c_22])).

cnf(c_8027,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_7998,c_6860])).

cnf(c_111387,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_111300,c_8027])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_676,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_2])).

cnf(c_111605,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_111387,c_676])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_654,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6331,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_654])).

cnf(c_902,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6581,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6331,c_19,c_18,c_902])).

cnf(c_115438,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_111605,c_6581])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_896,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_16,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_115438,c_111605,c_896,c_16,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 39.33/5.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.33/5.50  
% 39.33/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.33/5.50  
% 39.33/5.50  ------  iProver source info
% 39.33/5.50  
% 39.33/5.50  git: date: 2020-06-30 10:37:57 +0100
% 39.33/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.33/5.50  git: non_committed_changes: false
% 39.33/5.50  git: last_make_outside_of_git: false
% 39.33/5.50  
% 39.33/5.50  ------ 
% 39.33/5.50  ------ Parsing...
% 39.33/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.33/5.50  ------ Proving...
% 39.33/5.50  ------ Problem Properties 
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  clauses                                 21
% 39.33/5.50  conjectures                             5
% 39.33/5.50  EPR                                     2
% 39.33/5.50  Horn                                    20
% 39.33/5.50  unary                                   10
% 39.33/5.50  binary                                  5
% 39.33/5.50  lits                                    41
% 39.33/5.50  lits eq                                 15
% 39.33/5.50  fd_pure                                 0
% 39.33/5.50  fd_pseudo                               0
% 39.33/5.50  fd_cond                                 1
% 39.33/5.50  fd_pseudo_cond                          0
% 39.33/5.50  AC symbols                              0
% 39.33/5.50  
% 39.33/5.50  ------ Input Options Time Limit: Unbounded
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  ------ 
% 39.33/5.50  Current options:
% 39.33/5.50  ------ 
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  ------ Proving...
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  % SZS status Theorem for theBenchmark.p
% 39.33/5.50  
% 39.33/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 39.33/5.50  
% 39.33/5.50  fof(f1,axiom,(
% 39.33/5.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f21,plain,(
% 39.33/5.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 39.33/5.50    inference(rectify,[],[f1])).
% 39.33/5.50  
% 39.33/5.50  fof(f40,plain,(
% 39.33/5.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 39.33/5.50    inference(cnf_transformation,[],[f21])).
% 39.33/5.50  
% 39.33/5.50  fof(f14,axiom,(
% 39.33/5.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f53,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f14])).
% 39.33/5.50  
% 39.33/5.50  fof(f66,plain,(
% 39.33/5.50    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 39.33/5.50    inference(definition_unfolding,[],[f40,f53])).
% 39.33/5.50  
% 39.33/5.50  fof(f5,axiom,(
% 39.33/5.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f44,plain,(
% 39.33/5.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f5])).
% 39.33/5.50  
% 39.33/5.50  fof(f2,axiom,(
% 39.33/5.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f41,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f2])).
% 39.33/5.50  
% 39.33/5.50  fof(f64,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 39.33/5.50    inference(definition_unfolding,[],[f41,f53])).
% 39.33/5.50  
% 39.33/5.50  fof(f69,plain,(
% 39.33/5.50    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 39.33/5.50    inference(definition_unfolding,[],[f44,f64])).
% 39.33/5.50  
% 39.33/5.50  fof(f3,axiom,(
% 39.33/5.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f22,plain,(
% 39.33/5.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.33/5.50    inference(ennf_transformation,[],[f3])).
% 39.33/5.50  
% 39.33/5.50  fof(f42,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f22])).
% 39.33/5.50  
% 39.33/5.50  fof(f67,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 39.33/5.50    inference(definition_unfolding,[],[f42,f53])).
% 39.33/5.50  
% 39.33/5.50  fof(f10,axiom,(
% 39.33/5.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f49,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f10])).
% 39.33/5.50  
% 39.33/5.50  fof(f6,axiom,(
% 39.33/5.50    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f23,plain,(
% 39.33/5.50    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 39.33/5.50    inference(ennf_transformation,[],[f6])).
% 39.33/5.50  
% 39.33/5.50  fof(f45,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f23])).
% 39.33/5.50  
% 39.33/5.50  fof(f70,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 39.33/5.50    inference(definition_unfolding,[],[f45,f64])).
% 39.33/5.50  
% 39.33/5.50  fof(f11,axiom,(
% 39.33/5.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f50,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f11])).
% 39.33/5.50  
% 39.33/5.50  fof(f9,axiom,(
% 39.33/5.50    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f48,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f9])).
% 39.33/5.50  
% 39.33/5.50  fof(f65,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 39.33/5.50    inference(definition_unfolding,[],[f48,f64])).
% 39.33/5.50  
% 39.33/5.50  fof(f73,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.33/5.50    inference(definition_unfolding,[],[f50,f65])).
% 39.33/5.50  
% 39.33/5.50  fof(f8,axiom,(
% 39.33/5.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f47,plain,(
% 39.33/5.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f8])).
% 39.33/5.50  
% 39.33/5.50  fof(f72,plain,(
% 39.33/5.50    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 39.33/5.50    inference(definition_unfolding,[],[f47,f65])).
% 39.33/5.50  
% 39.33/5.50  fof(f19,conjecture,(
% 39.33/5.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f20,negated_conjecture,(
% 39.33/5.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 39.33/5.50    inference(negated_conjecture,[],[f19])).
% 39.33/5.50  
% 39.33/5.50  fof(f33,plain,(
% 39.33/5.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 39.33/5.50    inference(ennf_transformation,[],[f20])).
% 39.33/5.50  
% 39.33/5.50  fof(f34,plain,(
% 39.33/5.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.33/5.50    inference(flattening,[],[f33])).
% 39.33/5.50  
% 39.33/5.50  fof(f35,plain,(
% 39.33/5.50    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.33/5.50    inference(nnf_transformation,[],[f34])).
% 39.33/5.50  
% 39.33/5.50  fof(f36,plain,(
% 39.33/5.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.33/5.50    inference(flattening,[],[f35])).
% 39.33/5.50  
% 39.33/5.50  fof(f38,plain,(
% 39.33/5.50    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.33/5.50    introduced(choice_axiom,[])).
% 39.33/5.50  
% 39.33/5.50  fof(f37,plain,(
% 39.33/5.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 39.33/5.50    introduced(choice_axiom,[])).
% 39.33/5.50  
% 39.33/5.50  fof(f39,plain,(
% 39.33/5.50    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 39.33/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 39.33/5.50  
% 39.33/5.50  fof(f62,plain,(
% 39.33/5.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 39.33/5.50    inference(cnf_transformation,[],[f39])).
% 39.33/5.50  
% 39.33/5.50  fof(f61,plain,(
% 39.33/5.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.33/5.50    inference(cnf_transformation,[],[f39])).
% 39.33/5.50  
% 39.33/5.50  fof(f15,axiom,(
% 39.33/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f27,plain,(
% 39.33/5.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.33/5.50    inference(ennf_transformation,[],[f15])).
% 39.33/5.50  
% 39.33/5.50  fof(f28,plain,(
% 39.33/5.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.33/5.50    inference(flattening,[],[f27])).
% 39.33/5.50  
% 39.33/5.50  fof(f54,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f28])).
% 39.33/5.50  
% 39.33/5.50  fof(f60,plain,(
% 39.33/5.50    l1_pre_topc(sK0)),
% 39.33/5.50    inference(cnf_transformation,[],[f39])).
% 39.33/5.50  
% 39.33/5.50  fof(f13,axiom,(
% 39.33/5.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f26,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.33/5.50    inference(ennf_transformation,[],[f13])).
% 39.33/5.50  
% 39.33/5.50  fof(f52,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f26])).
% 39.33/5.50  
% 39.33/5.50  fof(f75,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.33/5.50    inference(definition_unfolding,[],[f52,f64])).
% 39.33/5.50  
% 39.33/5.50  fof(f18,axiom,(
% 39.33/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f32,plain,(
% 39.33/5.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.33/5.50    inference(ennf_transformation,[],[f18])).
% 39.33/5.50  
% 39.33/5.50  fof(f58,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f32])).
% 39.33/5.50  
% 39.33/5.50  fof(f16,axiom,(
% 39.33/5.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f29,plain,(
% 39.33/5.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.33/5.50    inference(ennf_transformation,[],[f16])).
% 39.33/5.50  
% 39.33/5.50  fof(f30,plain,(
% 39.33/5.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.33/5.50    inference(flattening,[],[f29])).
% 39.33/5.50  
% 39.33/5.50  fof(f56,plain,(
% 39.33/5.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f30])).
% 39.33/5.50  
% 39.33/5.50  fof(f12,axiom,(
% 39.33/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f24,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 39.33/5.50    inference(ennf_transformation,[],[f12])).
% 39.33/5.50  
% 39.33/5.50  fof(f25,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.33/5.50    inference(flattening,[],[f24])).
% 39.33/5.50  
% 39.33/5.50  fof(f51,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f25])).
% 39.33/5.50  
% 39.33/5.50  fof(f74,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.33/5.50    inference(definition_unfolding,[],[f51,f65])).
% 39.33/5.50  
% 39.33/5.50  fof(f7,axiom,(
% 39.33/5.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f46,plain,(
% 39.33/5.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.33/5.50    inference(cnf_transformation,[],[f7])).
% 39.33/5.50  
% 39.33/5.50  fof(f71,plain,(
% 39.33/5.50    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 39.33/5.50    inference(definition_unfolding,[],[f46,f64])).
% 39.33/5.50  
% 39.33/5.50  fof(f4,axiom,(
% 39.33/5.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f43,plain,(
% 39.33/5.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 39.33/5.50    inference(cnf_transformation,[],[f4])).
% 39.33/5.50  
% 39.33/5.50  fof(f68,plain,(
% 39.33/5.50    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 39.33/5.50    inference(definition_unfolding,[],[f43,f53])).
% 39.33/5.50  
% 39.33/5.50  fof(f17,axiom,(
% 39.33/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f31,plain,(
% 39.33/5.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.33/5.50    inference(ennf_transformation,[],[f17])).
% 39.33/5.50  
% 39.33/5.50  fof(f57,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f31])).
% 39.33/5.50  
% 39.33/5.50  fof(f55,plain,(
% 39.33/5.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f28])).
% 39.33/5.50  
% 39.33/5.50  fof(f63,plain,(
% 39.33/5.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 39.33/5.50    inference(cnf_transformation,[],[f39])).
% 39.33/5.50  
% 39.33/5.50  fof(f59,plain,(
% 39.33/5.50    v2_pre_topc(sK0)),
% 39.33/5.50    inference(cnf_transformation,[],[f39])).
% 39.33/5.50  
% 39.33/5.50  cnf(c_0,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 39.33/5.50      inference(cnf_transformation,[],[f66]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_3,plain,
% 39.33/5.50      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f69]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_662,plain,
% 39.33/5.50      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1755,plain,
% 39.33/5.50      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_0,c_662]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 39.33/5.50      inference(cnf_transformation,[],[f67]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_663,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 39.33/5.50      | r1_tarski(X0,X1) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2226,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(k5_xboole_0(X0,X0),X0)) = k5_xboole_0(X0,X0) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1755,c_663]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_7,plain,
% 39.33/5.50      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f49]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_4,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))
% 39.33/5.50      | k1_xboole_0 = X0 ),
% 39.33/5.50      inference(cnf_transformation,[],[f70]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_661,plain,
% 39.33/5.50      ( k1_xboole_0 = X0
% 39.33/5.50      | r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_3314,plain,
% 39.33/5.50      ( k1_xboole_0 = X0
% 39.33/5.50      | r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X0,X1)))) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_7,c_661]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_15125,plain,
% 39.33/5.50      ( k5_xboole_0(X0,X0) = k1_xboole_0
% 39.33/5.50      | r1_tarski(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X0))) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2226,c_3314]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_8,plain,
% 39.33/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.33/5.50      inference(cnf_transformation,[],[f73]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1208,plain,
% 39.33/5.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = k3_tarski(k2_tarski(X0,X0)) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_15154,plain,
% 39.33/5.50      ( k5_xboole_0(X0,X0) = k1_xboole_0
% 39.33/5.50      | r1_tarski(k5_xboole_0(X0,X0),k3_tarski(k2_tarski(X0,X0))) != iProver_top ),
% 39.33/5.50      inference(light_normalisation,[status(thm)],[c_15125,c_1208]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1758,plain,
% 39.33/5.50      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))),X0) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_7,c_662]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_15130,plain,
% 39.33/5.50      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X0) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2226,c_1758]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_15141,plain,
% 39.33/5.50      ( r1_tarski(k3_tarski(k2_tarski(X0,X0)),X0) = iProver_top ),
% 39.33/5.50      inference(light_normalisation,[status(thm)],[c_15130,c_1208]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_19022,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X0)),X0)) = k3_tarski(k2_tarski(X0,X0)) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_15141,c_663]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_23756,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X0)))) = k3_tarski(k2_tarski(X0,X0)) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_7,c_19022]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6,plain,
% 39.33/5.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
% 39.33/5.50      inference(cnf_transformation,[],[f72]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_660,plain,
% 39.33/5.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_684,plain,
% 39.33/5.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 39.33/5.50      inference(demodulation,[status(thm)],[c_8,c_660]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2222,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_684,c_663]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_23795,plain,
% 39.33/5.50      ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
% 39.33/5.50      inference(demodulation,[status(thm)],[c_23756,c_2222]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_111297,plain,
% 39.33/5.50      ( k5_xboole_0(X0,X0) = k1_xboole_0
% 39.33/5.50      | r1_tarski(k5_xboole_0(X0,X0),X0) != iProver_top ),
% 39.33/5.50      inference(light_normalisation,[status(thm)],[c_15154,c_23795]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_111300,plain,
% 39.33/5.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.33/5.50      inference(forward_subsumption_resolution,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_111297,c_1755]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_17,negated_conjecture,
% 39.33/5.50      ( v4_pre_topc(sK1,sK0)
% 39.33/5.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.33/5.50      inference(cnf_transformation,[],[f62]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_651,plain,
% 39.33/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.33/5.50      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_18,negated_conjecture,
% 39.33/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.33/5.50      inference(cnf_transformation,[],[f61]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_650,plain,
% 39.33/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_12,plain,
% 39.33/5.50      ( ~ v4_pre_topc(X0,X1)
% 39.33/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.33/5.50      | ~ l1_pre_topc(X1)
% 39.33/5.50      | k2_pre_topc(X1,X0) = X0 ),
% 39.33/5.50      inference(cnf_transformation,[],[f54]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_656,plain,
% 39.33/5.50      ( k2_pre_topc(X0,X1) = X1
% 39.33/5.50      | v4_pre_topc(X1,X0) != iProver_top
% 39.33/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.33/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6307,plain,
% 39.33/5.50      ( k2_pre_topc(sK0,sK1) = sK1
% 39.33/5.50      | v4_pre_topc(sK1,sK0) != iProver_top
% 39.33/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_650,c_656]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_19,negated_conjecture,
% 39.33/5.50      ( l1_pre_topc(sK0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f60]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_22,plain,
% 39.33/5.50      ( l1_pre_topc(sK0) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6573,plain,
% 39.33/5.50      ( v4_pre_topc(sK1,sK0) != iProver_top
% 39.33/5.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.33/5.50      inference(global_propositional_subsumption,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_6307,c_22]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6574,plain,
% 39.33/5.50      ( k2_pre_topc(sK0,sK1) = sK1
% 39.33/5.50      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.33/5.50      inference(renaming,[status(thm)],[c_6573]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6579,plain,
% 39.33/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.33/5.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_651,c_6574]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_10,plain,
% 39.33/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.33/5.50      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 39.33/5.50      inference(cnf_transformation,[],[f75]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_658,plain,
% 39.33/5.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 39.33/5.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1929,plain,
% 39.33/5.50      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_650,c_658]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2446,plain,
% 39.33/5.50      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1929,c_662]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2590,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2446,c_663]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2921,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_7,c_2590]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6814,plain,
% 39.33/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
% 39.33/5.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_6579,c_2921]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_7166,plain,
% 39.33/5.50      ( k2_pre_topc(sK0,sK1) = sK1
% 39.33/5.50      | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_6579,c_6814]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1210,plain,
% 39.33/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_7998,plain,
% 39.33/5.50      ( k2_pre_topc(sK0,sK1) = sK1
% 39.33/5.50      | k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_7166,c_1210]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_15,plain,
% 39.33/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.33/5.50      | ~ l1_pre_topc(X1)
% 39.33/5.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f58]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_653,plain,
% 39.33/5.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 39.33/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.33/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6148,plain,
% 39.33/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 39.33/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_650,c_653]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_13,plain,
% 39.33/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.33/5.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.33/5.50      | ~ l1_pre_topc(X1) ),
% 39.33/5.50      inference(cnf_transformation,[],[f56]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_655,plain,
% 39.33/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.33/5.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 39.33/5.50      | l1_pre_topc(X1) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_9,plain,
% 39.33/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.33/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.33/5.50      | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f74]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_659,plain,
% 39.33/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
% 39.33/5.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 39.33/5.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_734,plain,
% 39.33/5.50      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 39.33/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.33/5.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 39.33/5.50      inference(light_normalisation,[status(thm)],[c_659,c_8]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_4653,plain,
% 39.33/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 39.33/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_650,c_734]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_4675,plain,
% 39.33/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 39.33/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.33/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_655,c_4653]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_4961,plain,
% 39.33/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.33/5.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 39.33/5.50      inference(global_propositional_subsumption,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_4675,c_22]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_4962,plain,
% 39.33/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 39.33/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.33/5.50      inference(renaming,[status(thm)],[c_4961]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_4970,plain,
% 39.33/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_650,c_4962]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6151,plain,
% 39.33/5.50      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 39.33/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.33/5.50      inference(demodulation,[status(thm)],[c_6148,c_4970]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6860,plain,
% 39.33/5.50      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 39.33/5.50      inference(global_propositional_subsumption,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_6151,c_22]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_8027,plain,
% 39.33/5.50      ( k2_pre_topc(sK0,sK1) = sK1
% 39.33/5.50      | k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 39.33/5.50      inference(light_normalisation,[status(thm)],[c_7998,c_6860]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_111387,plain,
% 39.33/5.50      ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
% 39.33/5.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.33/5.50      inference(demodulation,[status(thm)],[c_111300,c_8027]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_5,plain,
% 39.33/5.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 39.33/5.50      inference(cnf_transformation,[],[f71]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2,plain,
% 39.33/5.50      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 39.33/5.50      inference(cnf_transformation,[],[f68]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_676,plain,
% 39.33/5.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.33/5.50      inference(light_normalisation,[status(thm)],[c_5,c_2]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_111605,plain,
% 39.33/5.50      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 39.33/5.50      inference(demodulation,[status(thm)],[c_111387,c_676]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_14,plain,
% 39.33/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.33/5.50      | ~ l1_pre_topc(X1)
% 39.33/5.50      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f57]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_654,plain,
% 39.33/5.50      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 39.33/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.33/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6331,plain,
% 39.33/5.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.33/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_650,c_654]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_902,plain,
% 39.33/5.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.33/5.50      | ~ l1_pre_topc(sK0)
% 39.33/5.50      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_14]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6581,plain,
% 39.33/5.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.33/5.50      inference(global_propositional_subsumption,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_6331,c_19,c_18,c_902]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_115438,plain,
% 39.33/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.33/5.50      inference(demodulation,[status(thm)],[c_111605,c_6581]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_11,plain,
% 39.33/5.50      ( v4_pre_topc(X0,X1)
% 39.33/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.33/5.50      | ~ l1_pre_topc(X1)
% 39.33/5.50      | ~ v2_pre_topc(X1)
% 39.33/5.50      | k2_pre_topc(X1,X0) != X0 ),
% 39.33/5.50      inference(cnf_transformation,[],[f55]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_896,plain,
% 39.33/5.50      ( v4_pre_topc(sK1,sK0)
% 39.33/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.33/5.50      | ~ l1_pre_topc(sK0)
% 39.33/5.50      | ~ v2_pre_topc(sK0)
% 39.33/5.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_11]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_16,negated_conjecture,
% 39.33/5.50      ( ~ v4_pre_topc(sK1,sK0)
% 39.33/5.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 39.33/5.50      inference(cnf_transformation,[],[f63]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_20,negated_conjecture,
% 39.33/5.50      ( v2_pre_topc(sK0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f59]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(contradiction,plain,
% 39.33/5.50      ( $false ),
% 39.33/5.50      inference(minisat,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_115438,c_111605,c_896,c_16,c_18,c_19,c_20]) ).
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.33/5.50  
% 39.33/5.50  ------                               Statistics
% 39.33/5.50  
% 39.33/5.50  ------ Selected
% 39.33/5.50  
% 39.33/5.50  total_time:                             4.669
% 39.33/5.50  
%------------------------------------------------------------------------------
