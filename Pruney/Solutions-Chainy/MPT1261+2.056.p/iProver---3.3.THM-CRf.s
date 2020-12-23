%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:32 EST 2020

% Result     : Theorem 42.46s
% Output     : CNFRefutation 42.46s
% Verified   : 
% Statistics : Number of formulae       :  204 (5001 expanded)
%              Number of clauses        :  127 (1483 expanded)
%              Number of leaves         :   22 (1261 expanded)
%              Depth                    :   27
%              Number of atoms          :  431 (12769 expanded)
%              Number of equality atoms :  235 (5429 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f50,f52,f57,f70])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f48,f52,f57])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_788,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_795,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_796,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6462,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_796])).

cnf(c_2394,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_796])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_797,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_147])).

cnf(c_783,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_111395,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_797,c_783])).

cnf(c_113039,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_111395])).

cnf(c_113567,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6462,c_113039])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_114727,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_113567,c_24])).

cnf(c_114728,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_114727])).

cnf(c_114737,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_788,c_114728])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_793,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4607,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_793])).

cnf(c_1049,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5083,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4607,c_21,c_20,c_1049])).

cnf(c_114739,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_114737,c_5083])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_791,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2203,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_791])).

cnf(c_1052,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2827,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2203,c_21,c_20,c_1052])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_191,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_147])).

cnf(c_782,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_2602,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_2394,c_782])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_798,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2834,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2602,c_798])).

cnf(c_3134,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2827,c_2834])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_800,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3756,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3134,c_800])).

cnf(c_5,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7280,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k1_xboole_0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3756,c_5])).

cnf(c_2,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7690,plain,
    ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7280,c_2])).

cnf(c_6,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2832,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_2602])).

cnf(c_7800,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7690,c_2832])).

cnf(c_19,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_789,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_792,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3393,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_792])).

cnf(c_3945,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3393,c_24])).

cnf(c_3946,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_3945])).

cnf(c_3951,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))) = k1_xboole_0
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3946,c_800])).

cnf(c_4064,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_789,c_3951])).

cnf(c_4071,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)),k1_xboole_0)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4064,c_5])).

cnf(c_4074,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4071,c_2])).

cnf(c_15245,plain,
    ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7800,c_4074])).

cnf(c_3,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1203,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_3])).

cnf(c_20429,plain,
    ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_15245,c_1203])).

cnf(c_114904,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_114739,c_20429])).

cnf(c_7786,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6,c_7690])).

cnf(c_1061,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_1205,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_1061])).

cnf(c_1351,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_1205])).

cnf(c_1974,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_798])).

cnf(c_1494,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_1351,c_5])).

cnf(c_1624,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1494,c_1061])).

cnf(c_1983,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1974,c_1624])).

cnf(c_1996,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1983,c_782])).

cnf(c_8685,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7786,c_1996])).

cnf(c_3751,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_798,c_800])).

cnf(c_47537,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(k7_subset_1(X0,X0,X1),X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3751,c_1996])).

cnf(c_47574,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_47537])).

cnf(c_1977,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2))) = k7_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_798,c_782])).

cnf(c_7441,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) = k7_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_6,c_1977])).

cnf(c_11645,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X2,k7_subset_1(X0,X0,X1)))) = k7_subset_1(X0,k7_subset_1(X0,X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_7441,c_1996])).

cnf(c_47964,plain,
    ( k7_subset_1(X0,k7_subset_1(X0,X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_47574,c_11645])).

cnf(c_7459,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)),k7_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1977,c_5])).

cnf(c_12486,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k7_subset_1(X0,X0,X1),X2)),k7_subset_1(X0,k7_subset_1(X0,X0,X1),X2))) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7459,c_1996])).

cnf(c_12490,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k7_subset_1(X1,X1,X2))),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X0))) = k7_subset_1(X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_6,c_12486])).

cnf(c_48053,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))),k1_xboole_0)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_47964,c_12490])).

cnf(c_49794,plain,
    ( k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_48053,c_2])).

cnf(c_49965,plain,
    ( k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_49794,c_3])).

cnf(c_51553,plain,
    ( k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = sK1 ),
    inference(superposition,[status(thm)],[c_8685,c_49965])).

cnf(c_117396,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_114904,c_51553])).

cnf(c_117438,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_117396,c_114739])).

cnf(c_14,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_794,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6373,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_794])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1009,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1010,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_6818,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6373,c_23,c_24,c_25,c_1010])).

cnf(c_119248,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_117438,c_6818])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_147])).

cnf(c_785,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_46201,plain,
    ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_785,c_1996])).

cnf(c_46217,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3946,c_46201])).

cnf(c_8620,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1996,c_2602])).

cnf(c_9414,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_8620,c_2827])).

cnf(c_46270,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_46217,c_9414])).

cnf(c_119385,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_119248,c_46270])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_189,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_147])).

cnf(c_784,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_40958,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3946,c_784])).

cnf(c_119386,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_119248,c_40958])).

cnf(c_119405,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_119385,c_119386])).

cnf(c_46211,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3134,c_46201])).

cnf(c_46299,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_46211,c_8685])).

cnf(c_130517,plain,
    ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_119405,c_46299])).

cnf(c_18,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_790,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9347,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8620,c_790])).

cnf(c_35112,plain,
    ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8685,c_9347])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130517,c_119248,c_35112])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 42.46/6.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.46/6.02  
% 42.46/6.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 42.46/6.02  
% 42.46/6.02  ------  iProver source info
% 42.46/6.02  
% 42.46/6.02  git: date: 2020-06-30 10:37:57 +0100
% 42.46/6.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 42.46/6.02  git: non_committed_changes: false
% 42.46/6.02  git: last_make_outside_of_git: false
% 42.46/6.02  
% 42.46/6.02  ------ 
% 42.46/6.02  ------ Parsing...
% 42.46/6.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 42.46/6.02  
% 42.46/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 42.46/6.02  
% 42.46/6.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 42.46/6.02  
% 42.46/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 42.46/6.02  ------ Proving...
% 42.46/6.02  ------ Problem Properties 
% 42.46/6.02  
% 42.46/6.02  
% 42.46/6.02  clauses                                 23
% 42.46/6.02  conjectures                             5
% 42.46/6.02  EPR                                     2
% 42.46/6.02  Horn                                    22
% 42.46/6.02  unary                                   8
% 42.46/6.02  binary                                  9
% 42.46/6.02  lits                                    46
% 42.46/6.02  lits eq                                 14
% 42.46/6.02  fd_pure                                 0
% 42.46/6.02  fd_pseudo                               0
% 42.46/6.02  fd_cond                                 0
% 42.46/6.02  fd_pseudo_cond                          0
% 42.46/6.02  AC symbols                              0
% 42.46/6.02  
% 42.46/6.02  ------ Input Options Time Limit: Unbounded
% 42.46/6.02  
% 42.46/6.02  
% 42.46/6.02  ------ 
% 42.46/6.02  Current options:
% 42.46/6.02  ------ 
% 42.46/6.02  
% 42.46/6.02  
% 42.46/6.02  
% 42.46/6.02  
% 42.46/6.02  ------ Proving...
% 42.46/6.02  
% 42.46/6.02  
% 42.46/6.02  % SZS status Theorem for theBenchmark.p
% 42.46/6.02  
% 42.46/6.02  % SZS output start CNFRefutation for theBenchmark.p
% 42.46/6.02  
% 42.46/6.02  fof(f20,conjecture,(
% 42.46/6.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f21,negated_conjecture,(
% 42.46/6.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 42.46/6.02    inference(negated_conjecture,[],[f20])).
% 42.46/6.02  
% 42.46/6.02  fof(f35,plain,(
% 42.46/6.02    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 42.46/6.02    inference(ennf_transformation,[],[f21])).
% 42.46/6.02  
% 42.46/6.02  fof(f36,plain,(
% 42.46/6.02    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.46/6.02    inference(flattening,[],[f35])).
% 42.46/6.02  
% 42.46/6.02  fof(f39,plain,(
% 42.46/6.02    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.46/6.02    inference(nnf_transformation,[],[f36])).
% 42.46/6.02  
% 42.46/6.02  fof(f40,plain,(
% 42.46/6.02    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.46/6.02    inference(flattening,[],[f39])).
% 42.46/6.02  
% 42.46/6.02  fof(f42,plain,(
% 42.46/6.02    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 42.46/6.02    introduced(choice_axiom,[])).
% 42.46/6.02  
% 42.46/6.02  fof(f41,plain,(
% 42.46/6.02    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 42.46/6.02    introduced(choice_axiom,[])).
% 42.46/6.02  
% 42.46/6.02  fof(f43,plain,(
% 42.46/6.02    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 42.46/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 42.46/6.02  
% 42.46/6.02  fof(f67,plain,(
% 42.46/6.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 42.46/6.02    inference(cnf_transformation,[],[f43])).
% 42.46/6.02  
% 42.46/6.02  fof(f15,axiom,(
% 42.46/6.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f27,plain,(
% 42.46/6.02    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 42.46/6.02    inference(ennf_transformation,[],[f15])).
% 42.46/6.02  
% 42.46/6.02  fof(f28,plain,(
% 42.46/6.02    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 42.46/6.02    inference(flattening,[],[f27])).
% 42.46/6.02  
% 42.46/6.02  fof(f60,plain,(
% 42.46/6.02    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f28])).
% 42.46/6.02  
% 42.46/6.02  fof(f14,axiom,(
% 42.46/6.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f38,plain,(
% 42.46/6.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 42.46/6.02    inference(nnf_transformation,[],[f14])).
% 42.46/6.02  
% 42.46/6.02  fof(f58,plain,(
% 42.46/6.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 42.46/6.02    inference(cnf_transformation,[],[f38])).
% 42.46/6.02  
% 42.46/6.02  fof(f59,plain,(
% 42.46/6.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f38])).
% 42.46/6.02  
% 42.46/6.02  fof(f11,axiom,(
% 42.46/6.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f24,plain,(
% 42.46/6.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 42.46/6.02    inference(ennf_transformation,[],[f11])).
% 42.46/6.02  
% 42.46/6.02  fof(f25,plain,(
% 42.46/6.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.46/6.02    inference(flattening,[],[f24])).
% 42.46/6.02  
% 42.46/6.02  fof(f55,plain,(
% 42.46/6.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.46/6.02    inference(cnf_transformation,[],[f25])).
% 42.46/6.02  
% 42.46/6.02  fof(f8,axiom,(
% 42.46/6.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f52,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 42.46/6.02    inference(cnf_transformation,[],[f8])).
% 42.46/6.02  
% 42.46/6.02  fof(f78,plain,(
% 42.46/6.02    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.46/6.02    inference(definition_unfolding,[],[f55,f52])).
% 42.46/6.02  
% 42.46/6.02  fof(f66,plain,(
% 42.46/6.02    l1_pre_topc(sK0)),
% 42.46/6.02    inference(cnf_transformation,[],[f43])).
% 42.46/6.02  
% 42.46/6.02  fof(f17,axiom,(
% 42.46/6.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f31,plain,(
% 42.46/6.02    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.46/6.02    inference(ennf_transformation,[],[f17])).
% 42.46/6.02  
% 42.46/6.02  fof(f62,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f31])).
% 42.46/6.02  
% 42.46/6.02  fof(f19,axiom,(
% 42.46/6.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f34,plain,(
% 42.46/6.02    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.46/6.02    inference(ennf_transformation,[],[f19])).
% 42.46/6.02  
% 42.46/6.02  fof(f64,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f34])).
% 42.46/6.02  
% 42.46/6.02  fof(f12,axiom,(
% 42.46/6.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f26,plain,(
% 42.46/6.02    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.46/6.02    inference(ennf_transformation,[],[f12])).
% 42.46/6.02  
% 42.46/6.02  fof(f56,plain,(
% 42.46/6.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.46/6.02    inference(cnf_transformation,[],[f26])).
% 42.46/6.02  
% 42.46/6.02  fof(f2,axiom,(
% 42.46/6.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f46,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 42.46/6.02    inference(cnf_transformation,[],[f2])).
% 42.46/6.02  
% 42.46/6.02  fof(f13,axiom,(
% 42.46/6.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f57,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 42.46/6.02    inference(cnf_transformation,[],[f13])).
% 42.46/6.02  
% 42.46/6.02  fof(f70,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 42.46/6.02    inference(definition_unfolding,[],[f46,f57])).
% 42.46/6.02  
% 42.46/6.02  fof(f79,plain,(
% 42.46/6.02    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.46/6.02    inference(definition_unfolding,[],[f56,f70])).
% 42.46/6.02  
% 42.46/6.02  fof(f5,axiom,(
% 42.46/6.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f49,plain,(
% 42.46/6.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f5])).
% 42.46/6.02  
% 42.46/6.02  fof(f75,plain,(
% 42.46/6.02    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 42.46/6.02    inference(definition_unfolding,[],[f49,f70])).
% 42.46/6.02  
% 42.46/6.02  fof(f1,axiom,(
% 42.46/6.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f37,plain,(
% 42.46/6.02    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 42.46/6.02    inference(nnf_transformation,[],[f1])).
% 42.46/6.02  
% 42.46/6.02  fof(f45,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f37])).
% 42.46/6.02  
% 42.46/6.02  fof(f71,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X0,X1)) )),
% 42.46/6.02    inference(definition_unfolding,[],[f45,f70])).
% 42.46/6.02  
% 42.46/6.02  fof(f6,axiom,(
% 42.46/6.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f50,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 42.46/6.02    inference(cnf_transformation,[],[f6])).
% 42.46/6.02  
% 42.46/6.02  fof(f76,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) )),
% 42.46/6.02    inference(definition_unfolding,[],[f50,f52,f57,f70])).
% 42.46/6.02  
% 42.46/6.02  fof(f3,axiom,(
% 42.46/6.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f47,plain,(
% 42.46/6.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 42.46/6.02    inference(cnf_transformation,[],[f3])).
% 42.46/6.02  
% 42.46/6.02  fof(f73,plain,(
% 42.46/6.02    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 42.46/6.02    inference(definition_unfolding,[],[f47,f52])).
% 42.46/6.02  
% 42.46/6.02  fof(f7,axiom,(
% 42.46/6.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f51,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f7])).
% 42.46/6.02  
% 42.46/6.02  fof(f68,plain,(
% 42.46/6.02    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 42.46/6.02    inference(cnf_transformation,[],[f43])).
% 42.46/6.02  
% 42.46/6.02  fof(f18,axiom,(
% 42.46/6.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f32,plain,(
% 42.46/6.02    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.46/6.02    inference(ennf_transformation,[],[f18])).
% 42.46/6.02  
% 42.46/6.02  fof(f33,plain,(
% 42.46/6.02    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.46/6.02    inference(flattening,[],[f32])).
% 42.46/6.02  
% 42.46/6.02  fof(f63,plain,(
% 42.46/6.02    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f33])).
% 42.46/6.02  
% 42.46/6.02  fof(f4,axiom,(
% 42.46/6.02    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f48,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 42.46/6.02    inference(cnf_transformation,[],[f4])).
% 42.46/6.02  
% 42.46/6.02  fof(f74,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 42.46/6.02    inference(definition_unfolding,[],[f48,f52,f57])).
% 42.46/6.02  
% 42.46/6.02  fof(f16,axiom,(
% 42.46/6.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f29,plain,(
% 42.46/6.02    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 42.46/6.02    inference(ennf_transformation,[],[f16])).
% 42.46/6.02  
% 42.46/6.02  fof(f30,plain,(
% 42.46/6.02    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 42.46/6.02    inference(flattening,[],[f29])).
% 42.46/6.02  
% 42.46/6.02  fof(f61,plain,(
% 42.46/6.02    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 42.46/6.02    inference(cnf_transformation,[],[f30])).
% 42.46/6.02  
% 42.46/6.02  fof(f65,plain,(
% 42.46/6.02    v2_pre_topc(sK0)),
% 42.46/6.02    inference(cnf_transformation,[],[f43])).
% 42.46/6.02  
% 42.46/6.02  fof(f9,axiom,(
% 42.46/6.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f22,plain,(
% 42.46/6.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.46/6.02    inference(ennf_transformation,[],[f9])).
% 42.46/6.02  
% 42.46/6.02  fof(f53,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.46/6.02    inference(cnf_transformation,[],[f22])).
% 42.46/6.02  
% 42.46/6.02  fof(f77,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.46/6.02    inference(definition_unfolding,[],[f53,f70])).
% 42.46/6.02  
% 42.46/6.02  fof(f10,axiom,(
% 42.46/6.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 42.46/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 42.46/6.02  
% 42.46/6.02  fof(f23,plain,(
% 42.46/6.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.46/6.02    inference(ennf_transformation,[],[f10])).
% 42.46/6.02  
% 42.46/6.02  fof(f54,plain,(
% 42.46/6.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.46/6.02    inference(cnf_transformation,[],[f23])).
% 42.46/6.02  
% 42.46/6.02  fof(f69,plain,(
% 42.46/6.02    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 42.46/6.02    inference(cnf_transformation,[],[f43])).
% 42.46/6.02  
% 42.46/6.02  cnf(c_20,negated_conjecture,
% 42.46/6.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 42.46/6.02      inference(cnf_transformation,[],[f67]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_788,plain,
% 42.46/6.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_13,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.46/6.02      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 42.46/6.02      | ~ l1_pre_topc(X1) ),
% 42.46/6.02      inference(cnf_transformation,[],[f60]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_795,plain,
% 42.46/6.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 42.46/6.02      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 42.46/6.02      | l1_pre_topc(X1) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_12,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 42.46/6.02      inference(cnf_transformation,[],[f58]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_796,plain,
% 42.46/6.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 42.46/6.02      | r1_tarski(X0,X1) = iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_6462,plain,
% 42.46/6.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 42.46/6.02      | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
% 42.46/6.02      | l1_pre_topc(X1) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_795,c_796]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_2394,plain,
% 42.46/6.02      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_788,c_796]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_11,plain,
% 42.46/6.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 42.46/6.02      inference(cnf_transformation,[],[f59]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_797,plain,
% 42.46/6.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 42.46/6.02      | r1_tarski(X0,X1) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_9,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.46/6.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 42.46/6.02      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 42.46/6.02      inference(cnf_transformation,[],[f78]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_146,plain,
% 42.46/6.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 42.46/6.02      inference(prop_impl,[status(thm)],[c_11]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_147,plain,
% 42.46/6.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 42.46/6.02      inference(renaming,[status(thm)],[c_146]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_190,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.46/6.02      | ~ r1_tarski(X2,X1)
% 42.46/6.02      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 42.46/6.02      inference(bin_hyper_res,[status(thm)],[c_9,c_147]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_783,plain,
% 42.46/6.02      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 42.46/6.02      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 42.46/6.02      | r1_tarski(X1,X0) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_111395,plain,
% 42.46/6.02      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 42.46/6.02      | r1_tarski(X2,X0) != iProver_top
% 42.46/6.02      | r1_tarski(X1,X0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_797,c_783]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_113039,plain,
% 42.46/6.02      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 42.46/6.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_2394,c_111395]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_113567,plain,
% 42.46/6.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 42.46/6.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.46/6.02      | l1_pre_topc(sK0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6462,c_113039]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_21,negated_conjecture,
% 42.46/6.02      ( l1_pre_topc(sK0) ),
% 42.46/6.02      inference(cnf_transformation,[],[f66]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_24,plain,
% 42.46/6.02      ( l1_pre_topc(sK0) = iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_114727,plain,
% 42.46/6.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.46/6.02      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 42.46/6.02      inference(global_propositional_subsumption,
% 42.46/6.02                [status(thm)],
% 42.46/6.02                [c_113567,c_24]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_114728,plain,
% 42.46/6.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 42.46/6.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 42.46/6.02      inference(renaming,[status(thm)],[c_114727]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_114737,plain,
% 42.46/6.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_788,c_114728]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_15,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.46/6.02      | ~ l1_pre_topc(X1)
% 42.46/6.02      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 42.46/6.02      inference(cnf_transformation,[],[f62]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_793,plain,
% 42.46/6.02      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 42.46/6.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 42.46/6.02      | l1_pre_topc(X0) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_4607,plain,
% 42.46/6.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 42.46/6.02      | l1_pre_topc(sK0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_788,c_793]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1049,plain,
% 42.46/6.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 42.46/6.02      | ~ l1_pre_topc(sK0)
% 42.46/6.02      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 42.46/6.02      inference(instantiation,[status(thm)],[c_15]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_5083,plain,
% 42.46/6.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 42.46/6.02      inference(global_propositional_subsumption,
% 42.46/6.02                [status(thm)],
% 42.46/6.02                [c_4607,c_21,c_20,c_1049]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_114739,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 42.46/6.02      inference(light_normalisation,[status(thm)],[c_114737,c_5083]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_17,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.46/6.02      | ~ l1_pre_topc(X1)
% 42.46/6.02      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 42.46/6.02      inference(cnf_transformation,[],[f64]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_791,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 42.46/6.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 42.46/6.02      | l1_pre_topc(X0) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_2203,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 42.46/6.02      | l1_pre_topc(sK0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_788,c_791]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1052,plain,
% 42.46/6.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 42.46/6.02      | ~ l1_pre_topc(sK0)
% 42.46/6.02      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(instantiation,[status(thm)],[c_17]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_2827,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(global_propositional_subsumption,
% 42.46/6.02                [status(thm)],
% 42.46/6.02                [c_2203,c_21,c_20,c_1052]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_10,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.46/6.02      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 42.46/6.02      inference(cnf_transformation,[],[f79]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_191,plain,
% 42.46/6.02      ( ~ r1_tarski(X0,X1)
% 42.46/6.02      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 42.46/6.02      inference(bin_hyper_res,[status(thm)],[c_10,c_147]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_782,plain,
% 42.46/6.02      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 42.46/6.02      | r1_tarski(X0,X2) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_2602,plain,
% 42.46/6.02      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_2394,c_782]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_4,plain,
% 42.46/6.02      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 42.46/6.02      inference(cnf_transformation,[],[f75]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_798,plain,
% 42.46/6.02      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_2834,plain,
% 42.46/6.02      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_2602,c_798]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_3134,plain,
% 42.46/6.02      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_2827,c_2834]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_0,plain,
% 42.46/6.02      ( ~ r1_tarski(X0,X1)
% 42.46/6.02      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 42.46/6.02      inference(cnf_transformation,[],[f71]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_800,plain,
% 42.46/6.02      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0
% 42.46/6.02      | r1_tarski(X0,X1) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_3756,plain,
% 42.46/6.02      ( k5_xboole_0(k1_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))) = k1_xboole_0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_3134,c_800]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_5,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
% 42.46/6.02      inference(cnf_transformation,[],[f76]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_7280,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k1_xboole_0)) = k1_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_3756,c_5]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_2,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 42.46/6.02      inference(cnf_transformation,[],[f73]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_7690,plain,
% 42.46/6.02      ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_7280,c_2]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_6,plain,
% 42.46/6.02      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 42.46/6.02      inference(cnf_transformation,[],[f51]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_2832,plain,
% 42.46/6.02      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6,c_2602]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_7800,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_7690,c_2832]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_19,negated_conjecture,
% 42.46/6.02      ( v4_pre_topc(sK1,sK0)
% 42.46/6.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(cnf_transformation,[],[f68]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_789,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.46/6.02      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_16,plain,
% 42.46/6.02      ( ~ v4_pre_topc(X0,X1)
% 42.46/6.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.46/6.02      | r1_tarski(k2_tops_1(X1,X0),X0)
% 42.46/6.02      | ~ l1_pre_topc(X1) ),
% 42.46/6.02      inference(cnf_transformation,[],[f63]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_792,plain,
% 42.46/6.02      ( v4_pre_topc(X0,X1) != iProver_top
% 42.46/6.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 42.46/6.02      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 42.46/6.02      | l1_pre_topc(X1) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_3393,plain,
% 42.46/6.02      ( v4_pre_topc(sK1,sK0) != iProver_top
% 42.46/6.02      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 42.46/6.02      | l1_pre_topc(sK0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_788,c_792]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_3945,plain,
% 42.46/6.02      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 42.46/6.02      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.46/6.02      inference(global_propositional_subsumption,
% 42.46/6.02                [status(thm)],
% 42.46/6.02                [c_3393,c_24]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_3946,plain,
% 42.46/6.02      ( v4_pre_topc(sK1,sK0) != iProver_top
% 42.46/6.02      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 42.46/6.02      inference(renaming,[status(thm)],[c_3945]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_3951,plain,
% 42.46/6.02      ( k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))) = k1_xboole_0
% 42.46/6.02      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_3946,c_800]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_4064,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.46/6.02      | k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))) = k1_xboole_0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_789,c_3951]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_4071,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.46/6.02      | k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)),k1_xboole_0)) = k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_4064,c_5]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_4074,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.46/6.02      | k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_4071,c_2]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_15245,plain,
% 42.46/6.02      ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.46/6.02      | k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_7800,c_4074]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_3,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 42.46/6.02      inference(cnf_transformation,[],[f74]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1203,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6,c_3]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_20429,plain,
% 42.46/6.02      ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.46/6.02      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_15245,c_1203]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_114904,plain,
% 42.46/6.02      ( k2_pre_topc(sK0,sK1) = sK1
% 42.46/6.02      | k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_114739,c_20429]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_7786,plain,
% 42.46/6.02      ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6,c_7690]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1061,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1205,plain,
% 42.46/6.02      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_3,c_1061]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1351,plain,
% 42.46/6.02      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6,c_1205]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1974,plain,
% 42.46/6.02      ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_1351,c_798]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1494,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = X0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_1351,c_5]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1624,plain,
% 42.46/6.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_1494,c_1061]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1983,plain,
% 42.46/6.02      ( r1_tarski(X0,X0) = iProver_top ),
% 42.46/6.02      inference(light_normalisation,[status(thm)],[c_1974,c_1624]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1996,plain,
% 42.46/6.02      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_1983,c_782]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_8685,plain,
% 42.46/6.02      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_7786,c_1996]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_3751,plain,
% 42.46/6.02      ( k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0))) = k1_xboole_0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_798,c_800]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_47537,plain,
% 42.46/6.02      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(k7_subset_1(X0,X0,X1),X0))) = k1_xboole_0 ),
% 42.46/6.02      inference(light_normalisation,[status(thm)],[c_3751,c_1996]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_47574,plain,
% 42.46/6.02      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1)))) = k1_xboole_0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6,c_47537]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1977,plain,
% 42.46/6.02      ( k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2))) = k7_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_798,c_782]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_7441,plain,
% 42.46/6.02      ( k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) = k7_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6,c_1977]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_11645,plain,
% 42.46/6.02      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X2,k7_subset_1(X0,X0,X1)))) = k7_subset_1(X0,k7_subset_1(X0,X0,X1),X2) ),
% 42.46/6.02      inference(light_normalisation,[status(thm)],[c_7441,c_1996]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_47964,plain,
% 42.46/6.02      ( k7_subset_1(X0,k7_subset_1(X0,X0,X1),X0) = k1_xboole_0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_47574,c_11645]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_7459,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)),k7_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_1977,c_5]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_12486,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k7_subset_1(X0,X0,X1),X2)),k7_subset_1(X0,k7_subset_1(X0,X0,X1),X2))) = k7_subset_1(X0,X0,X1) ),
% 42.46/6.02      inference(light_normalisation,[status(thm)],[c_7459,c_1996]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_12490,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k7_subset_1(X1,X1,X2))),k7_subset_1(X1,k7_subset_1(X1,X1,X2),X0))) = k7_subset_1(X1,X1,X2) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_6,c_12486]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_48053,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))),k1_xboole_0)) = k7_subset_1(X0,X0,X1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_47964,c_12490]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_49794,plain,
% 42.46/6.02      ( k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_48053,c_2]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_49965,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))) = X0 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_49794,c_3]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_51553,plain,
% 42.46/6.02      ( k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = sK1 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_8685,c_49965]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_117396,plain,
% 42.46/6.02      ( k2_pre_topc(sK0,sK1) = sK1
% 42.46/6.02      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_114904,c_51553]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_117438,plain,
% 42.46/6.02      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_117396,c_114739]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_14,plain,
% 42.46/6.02      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 42.46/6.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 42.46/6.02      | ~ v2_pre_topc(X0)
% 42.46/6.02      | ~ l1_pre_topc(X0) ),
% 42.46/6.02      inference(cnf_transformation,[],[f61]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_794,plain,
% 42.46/6.02      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 42.46/6.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 42.46/6.02      | v2_pre_topc(X0) != iProver_top
% 42.46/6.02      | l1_pre_topc(X0) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_6373,plain,
% 42.46/6.02      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 42.46/6.02      | v2_pre_topc(sK0) != iProver_top
% 42.46/6.02      | l1_pre_topc(sK0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_788,c_794]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_22,negated_conjecture,
% 42.46/6.02      ( v2_pre_topc(sK0) ),
% 42.46/6.02      inference(cnf_transformation,[],[f65]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_23,plain,
% 42.46/6.02      ( v2_pre_topc(sK0) = iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_25,plain,
% 42.46/6.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1009,plain,
% 42.46/6.02      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 42.46/6.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 42.46/6.02      | ~ v2_pre_topc(sK0)
% 42.46/6.02      | ~ l1_pre_topc(sK0) ),
% 42.46/6.02      inference(instantiation,[status(thm)],[c_14]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_1010,plain,
% 42.46/6.02      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 42.46/6.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.46/6.02      | v2_pre_topc(sK0) != iProver_top
% 42.46/6.02      | l1_pre_topc(sK0) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_6818,plain,
% 42.46/6.02      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 42.46/6.02      inference(global_propositional_subsumption,
% 42.46/6.02                [status(thm)],
% 42.46/6.02                [c_6373,c_23,c_24,c_25,c_1010]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_119248,plain,
% 42.46/6.02      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_117438,c_6818]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_7,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.46/6.02      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 42.46/6.02      inference(cnf_transformation,[],[f77]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_188,plain,
% 42.46/6.02      ( ~ r1_tarski(X0,X1)
% 42.46/6.02      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 42.46/6.02      inference(bin_hyper_res,[status(thm)],[c_7,c_147]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_785,plain,
% 42.46/6.02      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 42.46/6.02      | r1_tarski(X1,X0) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_46201,plain,
% 42.46/6.02      ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
% 42.46/6.02      | r1_tarski(X1,X0) != iProver_top ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_785,c_1996]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_46217,plain,
% 42.46/6.02      ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
% 42.46/6.02      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_3946,c_46201]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_8620,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_1996,c_2602]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_9414,plain,
% 42.46/6.02      ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_8620,c_2827]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_46270,plain,
% 42.46/6.02      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 42.46/6.02      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.46/6.02      inference(light_normalisation,[status(thm)],[c_46217,c_9414]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_119385,plain,
% 42.46/6.02      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_119248,c_46270]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_8,plain,
% 42.46/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.46/6.02      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 42.46/6.02      inference(cnf_transformation,[],[f54]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_189,plain,
% 42.46/6.02      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 42.46/6.02      inference(bin_hyper_res,[status(thm)],[c_8,c_147]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_784,plain,
% 42.46/6.02      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 42.46/6.02      | r1_tarski(X1,X0) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_40958,plain,
% 42.46/6.02      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 42.46/6.02      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_3946,c_784]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_119386,plain,
% 42.46/6.02      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_119248,c_40958]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_119405,plain,
% 42.46/6.02      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_119385,c_119386]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_46211,plain,
% 42.46/6.02      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 42.46/6.02      inference(superposition,[status(thm)],[c_3134,c_46201]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_46299,plain,
% 42.46/6.02      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 42.46/6.02      inference(light_normalisation,[status(thm)],[c_46211,c_8685]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_130517,plain,
% 42.46/6.02      ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_119405,c_46299]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_18,negated_conjecture,
% 42.46/6.02      ( ~ v4_pre_topc(sK1,sK0)
% 42.46/6.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 42.46/6.02      inference(cnf_transformation,[],[f69]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_790,plain,
% 42.46/6.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 42.46/6.02      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.46/6.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_9347,plain,
% 42.46/6.02      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 42.46/6.02      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_8620,c_790]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(c_35112,plain,
% 42.46/6.02      ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 42.46/6.02      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.46/6.02      inference(demodulation,[status(thm)],[c_8685,c_9347]) ).
% 42.46/6.02  
% 42.46/6.02  cnf(contradiction,plain,
% 42.46/6.02      ( $false ),
% 42.46/6.02      inference(minisat,[status(thm)],[c_130517,c_119248,c_35112]) ).
% 42.46/6.02  
% 42.46/6.02  
% 42.46/6.02  % SZS output end CNFRefutation for theBenchmark.p
% 42.46/6.02  
% 42.46/6.02  ------                               Statistics
% 42.46/6.02  
% 42.46/6.02  ------ Selected
% 42.46/6.02  
% 42.46/6.02  total_time:                             5.071
% 42.46/6.02  
%------------------------------------------------------------------------------
