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
% DateTime   : Thu Dec  3 12:14:33 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 556 expanded)
%              Number of clauses        :   61 ( 144 expanded)
%              Number of leaves         :   17 ( 128 expanded)
%              Depth                    :   20
%              Number of atoms          :  305 (2389 expanded)
%              Number of equality atoms :  142 ( 786 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f37,f41,f44])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_578,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_585,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_587,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2091,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X2)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_587])).

cnf(c_9923,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_2091])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10798,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9923,c_17])).

cnf(c_10799,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10798])).

cnf(c_10807,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_578,c_10799])).

cnf(c_12,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_579,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_581,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_967,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_581])).

cnf(c_1322,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_967,c_17])).

cnf(c_1323,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1322])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_589,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1328,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_589])).

cnf(c_1425,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_579,c_1328])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_586,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1208,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_578,c_586])).

cnf(c_2,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_588,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1213,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_588])).

cnf(c_1622,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_1213])).

cnf(c_1631,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1622,c_589])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_855,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1637,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_1631,c_855])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_582,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1783,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_582])).

cnf(c_778,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2299,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1783,c_14,c_13,c_778])).

cnf(c_10809,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_10807,c_1637,c_2299])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_583,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2917,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_583])).

cnf(c_816,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3492,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2917,c_14,c_13,c_816])).

cnf(c_10822,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10809,c_3492])).

cnf(c_7,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_584,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3186,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_584])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_750,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_751,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_3496,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3186,c_16,c_17,c_18,c_751])).

cnf(c_10821,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10809,c_3496])).

cnf(c_11,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10822,c_10821,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:15:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.90/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/0.99  
% 3.90/0.99  ------  iProver source info
% 3.90/0.99  
% 3.90/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.90/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/0.99  git: non_committed_changes: false
% 3.90/0.99  git: last_make_outside_of_git: false
% 3.90/0.99  
% 3.90/0.99  ------ 
% 3.90/0.99  ------ Parsing...
% 3.90/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  ------ Proving...
% 3.90/0.99  ------ Problem Properties 
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  clauses                                 16
% 3.90/0.99  conjectures                             5
% 3.90/0.99  EPR                                     2
% 3.90/0.99  Horn                                    15
% 3.90/0.99  unary                                   6
% 3.90/0.99  binary                                  4
% 3.90/0.99  lits                                    34
% 3.90/0.99  lits eq                                 9
% 3.90/0.99  fd_pure                                 0
% 3.90/0.99  fd_pseudo                               0
% 3.90/0.99  fd_cond                                 0
% 3.90/0.99  fd_pseudo_cond                          0
% 3.90/0.99  AC symbols                              0
% 3.90/0.99  
% 3.90/0.99  ------ Input Options Time Limit: Unbounded
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ 
% 3.90/0.99  Current options:
% 3.90/0.99  ------ 
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  % SZS status Theorem for theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  fof(f15,conjecture,(
% 3.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f16,negated_conjecture,(
% 3.90/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.90/0.99    inference(negated_conjecture,[],[f15])).
% 3.90/0.99  
% 3.90/0.99  fof(f29,plain,(
% 3.90/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.90/0.99    inference(ennf_transformation,[],[f16])).
% 3.90/0.99  
% 3.90/0.99  fof(f30,plain,(
% 3.90/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.90/0.99    inference(flattening,[],[f29])).
% 3.90/0.99  
% 3.90/0.99  fof(f31,plain,(
% 3.90/0.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.90/0.99    inference(nnf_transformation,[],[f30])).
% 3.90/0.99  
% 3.90/0.99  fof(f32,plain,(
% 3.90/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.90/0.99    inference(flattening,[],[f31])).
% 3.90/0.99  
% 3.90/0.99  fof(f34,plain,(
% 3.90/0.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.90/0.99    introduced(choice_axiom,[])).
% 3.90/0.99  
% 3.90/0.99  fof(f33,plain,(
% 3.90/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.90/0.99    introduced(choice_axiom,[])).
% 3.90/0.99  
% 3.90/0.99  fof(f35,plain,(
% 3.90/0.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.90/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 3.90/0.99  
% 3.90/0.99  fof(f52,plain,(
% 3.90/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.90/0.99    inference(cnf_transformation,[],[f35])).
% 3.90/0.99  
% 3.90/0.99  fof(f10,axiom,(
% 3.90/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f21,plain,(
% 3.90/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.90/0.99    inference(ennf_transformation,[],[f10])).
% 3.90/0.99  
% 3.90/0.99  fof(f22,plain,(
% 3.90/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.90/0.99    inference(flattening,[],[f21])).
% 3.90/0.99  
% 3.90/0.99  fof(f45,plain,(
% 3.90/0.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f22])).
% 3.90/0.99  
% 3.90/0.99  fof(f7,axiom,(
% 3.90/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f18,plain,(
% 3.90/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.90/0.99    inference(ennf_transformation,[],[f7])).
% 3.90/0.99  
% 3.90/0.99  fof(f19,plain,(
% 3.90/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/0.99    inference(flattening,[],[f18])).
% 3.90/0.99  
% 3.90/0.99  fof(f42,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f19])).
% 3.90/0.99  
% 3.90/0.99  fof(f6,axiom,(
% 3.90/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f41,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f6])).
% 3.90/0.99  
% 3.90/0.99  fof(f59,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/0.99    inference(definition_unfolding,[],[f42,f41])).
% 3.90/0.99  
% 3.90/0.99  fof(f51,plain,(
% 3.90/0.99    l1_pre_topc(sK0)),
% 3.90/0.99    inference(cnf_transformation,[],[f35])).
% 3.90/0.99  
% 3.90/0.99  fof(f53,plain,(
% 3.90/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.90/0.99    inference(cnf_transformation,[],[f35])).
% 3.90/0.99  
% 3.90/0.99  fof(f14,axiom,(
% 3.90/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f27,plain,(
% 3.90/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/0.99    inference(ennf_transformation,[],[f14])).
% 3.90/0.99  
% 3.90/0.99  fof(f28,plain,(
% 3.90/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/0.99    inference(flattening,[],[f27])).
% 3.90/0.99  
% 3.90/0.99  fof(f49,plain,(
% 3.90/0.99    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f28])).
% 3.90/0.99  
% 3.90/0.99  fof(f3,axiom,(
% 3.90/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f17,plain,(
% 3.90/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.90/0.99    inference(ennf_transformation,[],[f3])).
% 3.90/0.99  
% 3.90/0.99  fof(f38,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f17])).
% 3.90/0.99  
% 3.90/0.99  fof(f9,axiom,(
% 3.90/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f44,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f9])).
% 3.90/0.99  
% 3.90/0.99  fof(f57,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.90/0.99    inference(definition_unfolding,[],[f38,f44])).
% 3.90/0.99  
% 3.90/0.99  fof(f8,axiom,(
% 3.90/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f20,plain,(
% 3.90/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/0.99    inference(ennf_transformation,[],[f8])).
% 3.90/0.99  
% 3.90/0.99  fof(f43,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f20])).
% 3.90/0.99  
% 3.90/0.99  fof(f1,axiom,(
% 3.90/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f36,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f1])).
% 3.90/0.99  
% 3.90/0.99  fof(f55,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.90/0.99    inference(definition_unfolding,[],[f36,f44])).
% 3.90/0.99  
% 3.90/0.99  fof(f60,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/0.99    inference(definition_unfolding,[],[f43,f55])).
% 3.90/0.99  
% 3.90/0.99  fof(f4,axiom,(
% 3.90/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f39,plain,(
% 3.90/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f4])).
% 3.90/0.99  
% 3.90/0.99  fof(f58,plain,(
% 3.90/0.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 3.90/0.99    inference(definition_unfolding,[],[f39,f55])).
% 3.90/0.99  
% 3.90/0.99  fof(f5,axiom,(
% 3.90/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f40,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f5])).
% 3.90/0.99  
% 3.90/0.99  fof(f2,axiom,(
% 3.90/0.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f37,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.90/0.99    inference(cnf_transformation,[],[f2])).
% 3.90/0.99  
% 3.90/0.99  fof(f56,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 3.90/0.99    inference(definition_unfolding,[],[f37,f41,f44])).
% 3.90/0.99  
% 3.90/0.99  fof(f13,axiom,(
% 3.90/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f26,plain,(
% 3.90/0.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/0.99    inference(ennf_transformation,[],[f13])).
% 3.90/0.99  
% 3.90/0.99  fof(f48,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f26])).
% 3.90/0.99  
% 3.90/0.99  fof(f12,axiom,(
% 3.90/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f25,plain,(
% 3.90/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/0.99    inference(ennf_transformation,[],[f12])).
% 3.90/0.99  
% 3.90/0.99  fof(f47,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f25])).
% 3.90/0.99  
% 3.90/0.99  fof(f11,axiom,(
% 3.90/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f23,plain,(
% 3.90/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.90/0.99    inference(ennf_transformation,[],[f11])).
% 3.90/0.99  
% 3.90/0.99  fof(f24,plain,(
% 3.90/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.99    inference(flattening,[],[f23])).
% 3.90/0.99  
% 3.90/0.99  fof(f46,plain,(
% 3.90/0.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f24])).
% 3.90/0.99  
% 3.90/0.99  fof(f50,plain,(
% 3.90/0.99    v2_pre_topc(sK0)),
% 3.90/0.99    inference(cnf_transformation,[],[f35])).
% 3.90/0.99  
% 3.90/0.99  fof(f54,plain,(
% 3.90/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.90/0.99    inference(cnf_transformation,[],[f35])).
% 3.90/0.99  
% 3.90/0.99  cnf(c_13,negated_conjecture,
% 3.90/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.90/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_578,plain,
% 3.90/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_6,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/0.99      | ~ l1_pre_topc(X1) ),
% 3.90/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_585,plain,
% 3.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.90/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.90/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_4,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.90/0.99      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.90/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_587,plain,
% 3.90/0.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2091,plain,
% 3.90/0.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X2)))
% 3.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_585,c_587]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9923,plain,
% 3.90/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_578,c_2091]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_14,negated_conjecture,
% 3.90/0.99      ( l1_pre_topc(sK0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_17,plain,
% 3.90/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10798,plain,
% 3.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_9923,c_17]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10799,plain,
% 3.90/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.90/0.99      inference(renaming,[status(thm)],[c_10798]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10807,plain,
% 3.90/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_578,c_10799]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_12,negated_conjecture,
% 3.90/0.99      ( v4_pre_topc(sK1,sK0)
% 3.90/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_579,plain,
% 3.90/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.90/0.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10,plain,
% 3.90/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/0.99      | r1_tarski(k2_tops_1(X1,X0),X0)
% 3.90/0.99      | ~ l1_pre_topc(X1) ),
% 3.90/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_581,plain,
% 3.90/0.99      ( v4_pre_topc(X0,X1) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.90/0.99      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.90/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_967,plain,
% 3.90/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.90/0.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.90/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_578,c_581]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1322,plain,
% 3.90/0.99      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.90/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_967,c_17]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1323,plain,
% 3.90/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.90/0.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.90/0.99      inference(renaming,[status(thm)],[c_1322]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1,plain,
% 3.90/0.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 3.90/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_589,plain,
% 3.90/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 3.90/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1328,plain,
% 3.90/0.99      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
% 3.90/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1323,c_589]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1425,plain,
% 3.90/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.90/0.99      | k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_579,c_1328]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_5,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/0.99      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.90/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_586,plain,
% 3.90/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1208,plain,
% 3.90/0.99      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_578,c_586]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2,plain,
% 3.90/0.99      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_588,plain,
% 3.90/0.99      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1213,plain,
% 3.90/0.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1208,c_588]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1622,plain,
% 3.90/0.99      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
% 3.90/0.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1425,c_1213]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1631,plain,
% 3.90/0.99      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/0.99      inference(forward_subsumption_resolution,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_1622,c_589]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3,plain,
% 3.90/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_0,plain,
% 3.90/0.99      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 3.90/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_855,plain,
% 3.90/0.99      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1637,plain,
% 3.90/0.99      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1631,c_855]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/0.99      | ~ l1_pre_topc(X1)
% 3.90/0.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_582,plain,
% 3.90/0.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1783,plain,
% 3.90/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.90/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_578,c_582]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_778,plain,
% 3.90/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/0.99      | ~ l1_pre_topc(sK0)
% 3.90/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.90/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2299,plain,
% 3.90/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_1783,c_14,c_13,c_778]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10809,plain,
% 3.90/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.90/0.99      inference(light_normalisation,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_10807,c_1637,c_2299]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_8,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/0.99      | ~ l1_pre_topc(X1)
% 3.90/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_583,plain,
% 3.90/0.99      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2917,plain,
% 3.90/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.90/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_578,c_583]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_816,plain,
% 3.90/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/0.99      | ~ l1_pre_topc(sK0)
% 3.90/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3492,plain,
% 3.90/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2917,c_14,c_13,c_816]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10822,plain,
% 3.90/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/0.99      inference(demodulation,[status(thm)],[c_10809,c_3492]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_7,plain,
% 3.90/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.90/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.90/0.99      | ~ v2_pre_topc(X0)
% 3.90/0.99      | ~ l1_pre_topc(X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_584,plain,
% 3.90/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/0.99      | v2_pre_topc(X0) != iProver_top
% 3.90/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3186,plain,
% 3.90/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.90/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.90/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_578,c_584]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_15,negated_conjecture,
% 3.90/0.99      ( v2_pre_topc(sK0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_16,plain,
% 3.90/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_18,plain,
% 3.90/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_750,plain,
% 3.90/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 3.90/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/0.99      | ~ v2_pre_topc(sK0)
% 3.90/0.99      | ~ l1_pre_topc(sK0) ),
% 3.90/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_751,plain,
% 3.90/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.90/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.90/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3496,plain,
% 3.90/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_3186,c_16,c_17,c_18,c_751]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10821,plain,
% 3.90/0.99      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.90/0.99      inference(demodulation,[status(thm)],[c_10809,c_3496]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_11,negated_conjecture,
% 3.90/0.99      ( ~ v4_pre_topc(sK1,sK0)
% 3.90/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.90/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_20,plain,
% 3.90/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.90/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(contradiction,plain,
% 3.90/0.99      ( $false ),
% 3.90/0.99      inference(minisat,[status(thm)],[c_10822,c_10821,c_20]) ).
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  ------                               Statistics
% 3.90/0.99  
% 3.90/0.99  ------ Selected
% 3.90/0.99  
% 3.90/0.99  total_time:                             0.402
% 3.90/0.99  
%------------------------------------------------------------------------------
