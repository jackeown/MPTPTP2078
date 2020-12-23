%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:39 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  160 (1255 expanded)
%              Number of clauses        :   97 ( 429 expanded)
%              Number of leaves         :   20 ( 255 expanded)
%              Depth                    :   24
%              Number of atoms          :  400 (4346 expanded)
%              Number of equality atoms :  173 (1398 expanded)
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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f46,f61])).

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

fof(f53,plain,(
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

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1300,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1303,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2365,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_1303])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1308,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_147,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_186,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_148])).

cnf(c_1299,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_2368,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1308,c_1299])).

cnf(c_2372,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2368,c_1299])).

cnf(c_3782,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(superposition,[status(thm)],[c_2365,c_2372])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1301,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4068,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3782,c_1301])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_286,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_287,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_1297,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_1751,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_1297])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1306,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2550,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1306])).

cnf(c_2992,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2550,c_1306])).

cnf(c_4385,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2365,c_2992])).

cnf(c_2567,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2568,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_4773,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4385,c_2568])).

cnf(c_4774,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4773])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_148])).

cnf(c_610,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_646,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_185,c_611])).

cnf(c_1294,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_15718,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2365,c_1294])).

cnf(c_16125,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4774,c_15718])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_1296,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_1547,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1300,c_1296])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1307,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2057,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1307])).

cnf(c_2060,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1301,c_2057])).

cnf(c_4081,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3782,c_2060])).

cnf(c_6,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1305,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1944,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1305,c_1307])).

cnf(c_3075,plain,
    ( k2_xboole_0(k7_subset_1(X0,X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2368,c_1944])).

cnf(c_9019,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4081,c_3075])).

cnf(c_9499,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_9019])).

cnf(c_16137,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16125,c_1547,c_9499])).

cnf(c_16163,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4068,c_16137])).

cnf(c_2549,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1306])).

cnf(c_2551,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_subset_1(X0,X0,X2),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2549,c_2368])).

cnf(c_16122,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(X0,X0,X1)) = k2_xboole_0(sK1,k7_subset_1(X0,X0,X1))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_15718])).

cnf(c_17805,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X0)) = k2_xboole_0(sK1,k7_subset_1(sK1,sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2365,c_16122])).

cnf(c_2284,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1944])).

cnf(c_3074,plain,
    ( k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_2368,c_2284])).

cnf(c_17832,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_17805,c_3074])).

cnf(c_18063,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_16163,c_17832])).

cnf(c_18064,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_18063,c_1547])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_1295,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1689,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1300,c_1295])).

cnf(c_18066,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_18064,c_1689])).

cnf(c_876,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1846,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_877,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1382,plain,
    ( k2_pre_topc(sK0,sK1) != X0
    | sK1 != X0
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_1518,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | sK1 = k2_pre_topc(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_886,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1333,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(sK1,sK0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_1369,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_265,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_266,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_266,c_18])).

cnf(c_271,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_518,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_271])).

cnf(c_519,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_61,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_57,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18066,c_18064,c_1846,c_1518,c_1369,c_519,c_61,c_57,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.60/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/1.52  
% 7.60/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.60/1.52  
% 7.60/1.52  ------  iProver source info
% 7.60/1.52  
% 7.60/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.60/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.60/1.52  git: non_committed_changes: false
% 7.60/1.52  git: last_make_outside_of_git: false
% 7.60/1.52  
% 7.60/1.52  ------ 
% 7.60/1.52  
% 7.60/1.52  ------ Input Options
% 7.60/1.52  
% 7.60/1.52  --out_options                           all
% 7.60/1.52  --tptp_safe_out                         true
% 7.60/1.52  --problem_path                          ""
% 7.60/1.52  --include_path                          ""
% 7.60/1.52  --clausifier                            res/vclausify_rel
% 7.60/1.52  --clausifier_options                    ""
% 7.60/1.52  --stdin                                 false
% 7.60/1.52  --stats_out                             all
% 7.60/1.52  
% 7.60/1.52  ------ General Options
% 7.60/1.52  
% 7.60/1.52  --fof                                   false
% 7.60/1.52  --time_out_real                         305.
% 7.60/1.52  --time_out_virtual                      -1.
% 7.60/1.52  --symbol_type_check                     false
% 7.60/1.52  --clausify_out                          false
% 7.60/1.52  --sig_cnt_out                           false
% 7.60/1.52  --trig_cnt_out                          false
% 7.60/1.52  --trig_cnt_out_tolerance                1.
% 7.60/1.52  --trig_cnt_out_sk_spl                   false
% 7.60/1.52  --abstr_cl_out                          false
% 7.60/1.52  
% 7.60/1.52  ------ Global Options
% 7.60/1.52  
% 7.60/1.52  --schedule                              default
% 7.60/1.52  --add_important_lit                     false
% 7.60/1.52  --prop_solver_per_cl                    1000
% 7.60/1.52  --min_unsat_core                        false
% 7.60/1.52  --soft_assumptions                      false
% 7.60/1.52  --soft_lemma_size                       3
% 7.60/1.52  --prop_impl_unit_size                   0
% 7.60/1.52  --prop_impl_unit                        []
% 7.60/1.52  --share_sel_clauses                     true
% 7.60/1.52  --reset_solvers                         false
% 7.60/1.52  --bc_imp_inh                            [conj_cone]
% 7.60/1.52  --conj_cone_tolerance                   3.
% 7.60/1.52  --extra_neg_conj                        none
% 7.60/1.52  --large_theory_mode                     true
% 7.60/1.52  --prolific_symb_bound                   200
% 7.60/1.52  --lt_threshold                          2000
% 7.60/1.52  --clause_weak_htbl                      true
% 7.60/1.52  --gc_record_bc_elim                     false
% 7.60/1.52  
% 7.60/1.52  ------ Preprocessing Options
% 7.60/1.52  
% 7.60/1.52  --preprocessing_flag                    true
% 7.60/1.52  --time_out_prep_mult                    0.1
% 7.60/1.52  --splitting_mode                        input
% 7.60/1.52  --splitting_grd                         true
% 7.60/1.52  --splitting_cvd                         false
% 7.60/1.52  --splitting_cvd_svl                     false
% 7.60/1.52  --splitting_nvd                         32
% 7.60/1.52  --sub_typing                            true
% 7.60/1.52  --prep_gs_sim                           true
% 7.60/1.52  --prep_unflatten                        true
% 7.60/1.52  --prep_res_sim                          true
% 7.60/1.52  --prep_upred                            true
% 7.60/1.52  --prep_sem_filter                       exhaustive
% 7.60/1.52  --prep_sem_filter_out                   false
% 7.60/1.52  --pred_elim                             true
% 7.60/1.52  --res_sim_input                         true
% 7.60/1.52  --eq_ax_congr_red                       true
% 7.60/1.52  --pure_diseq_elim                       true
% 7.60/1.52  --brand_transform                       false
% 7.60/1.52  --non_eq_to_eq                          false
% 7.60/1.52  --prep_def_merge                        true
% 7.60/1.52  --prep_def_merge_prop_impl              false
% 7.60/1.52  --prep_def_merge_mbd                    true
% 7.60/1.52  --prep_def_merge_tr_red                 false
% 7.60/1.52  --prep_def_merge_tr_cl                  false
% 7.60/1.52  --smt_preprocessing                     true
% 7.60/1.52  --smt_ac_axioms                         fast
% 7.60/1.52  --preprocessed_out                      false
% 7.60/1.52  --preprocessed_stats                    false
% 7.60/1.52  
% 7.60/1.52  ------ Abstraction refinement Options
% 7.60/1.52  
% 7.60/1.52  --abstr_ref                             []
% 7.60/1.52  --abstr_ref_prep                        false
% 7.60/1.52  --abstr_ref_until_sat                   false
% 7.60/1.52  --abstr_ref_sig_restrict                funpre
% 7.60/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.60/1.52  --abstr_ref_under                       []
% 7.60/1.52  
% 7.60/1.52  ------ SAT Options
% 7.60/1.52  
% 7.60/1.52  --sat_mode                              false
% 7.60/1.52  --sat_fm_restart_options                ""
% 7.60/1.52  --sat_gr_def                            false
% 7.60/1.52  --sat_epr_types                         true
% 7.60/1.52  --sat_non_cyclic_types                  false
% 7.60/1.52  --sat_finite_models                     false
% 7.60/1.52  --sat_fm_lemmas                         false
% 7.60/1.52  --sat_fm_prep                           false
% 7.60/1.52  --sat_fm_uc_incr                        true
% 7.60/1.52  --sat_out_model                         small
% 7.60/1.52  --sat_out_clauses                       false
% 7.60/1.52  
% 7.60/1.52  ------ QBF Options
% 7.60/1.52  
% 7.60/1.52  --qbf_mode                              false
% 7.60/1.52  --qbf_elim_univ                         false
% 7.60/1.52  --qbf_dom_inst                          none
% 7.60/1.52  --qbf_dom_pre_inst                      false
% 7.60/1.52  --qbf_sk_in                             false
% 7.60/1.52  --qbf_pred_elim                         true
% 7.60/1.52  --qbf_split                             512
% 7.60/1.52  
% 7.60/1.52  ------ BMC1 Options
% 7.60/1.52  
% 7.60/1.52  --bmc1_incremental                      false
% 7.60/1.52  --bmc1_axioms                           reachable_all
% 7.60/1.52  --bmc1_min_bound                        0
% 7.60/1.52  --bmc1_max_bound                        -1
% 7.60/1.52  --bmc1_max_bound_default                -1
% 7.60/1.52  --bmc1_symbol_reachability              true
% 7.60/1.52  --bmc1_property_lemmas                  false
% 7.60/1.52  --bmc1_k_induction                      false
% 7.60/1.52  --bmc1_non_equiv_states                 false
% 7.60/1.52  --bmc1_deadlock                         false
% 7.60/1.52  --bmc1_ucm                              false
% 7.60/1.52  --bmc1_add_unsat_core                   none
% 7.60/1.52  --bmc1_unsat_core_children              false
% 7.60/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.60/1.52  --bmc1_out_stat                         full
% 7.60/1.52  --bmc1_ground_init                      false
% 7.60/1.52  --bmc1_pre_inst_next_state              false
% 7.60/1.52  --bmc1_pre_inst_state                   false
% 7.60/1.52  --bmc1_pre_inst_reach_state             false
% 7.60/1.52  --bmc1_out_unsat_core                   false
% 7.60/1.52  --bmc1_aig_witness_out                  false
% 7.60/1.52  --bmc1_verbose                          false
% 7.60/1.52  --bmc1_dump_clauses_tptp                false
% 7.60/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.60/1.52  --bmc1_dump_file                        -
% 7.60/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.60/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.60/1.52  --bmc1_ucm_extend_mode                  1
% 7.60/1.52  --bmc1_ucm_init_mode                    2
% 7.60/1.52  --bmc1_ucm_cone_mode                    none
% 7.60/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.60/1.52  --bmc1_ucm_relax_model                  4
% 7.60/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.60/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.60/1.52  --bmc1_ucm_layered_model                none
% 7.60/1.52  --bmc1_ucm_max_lemma_size               10
% 7.60/1.52  
% 7.60/1.52  ------ AIG Options
% 7.60/1.52  
% 7.60/1.52  --aig_mode                              false
% 7.60/1.52  
% 7.60/1.52  ------ Instantiation Options
% 7.60/1.52  
% 7.60/1.52  --instantiation_flag                    true
% 7.60/1.52  --inst_sos_flag                         true
% 7.60/1.52  --inst_sos_phase                        true
% 7.60/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.60/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.60/1.52  --inst_lit_sel_side                     num_symb
% 7.60/1.52  --inst_solver_per_active                1400
% 7.60/1.52  --inst_solver_calls_frac                1.
% 7.60/1.52  --inst_passive_queue_type               priority_queues
% 7.60/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.60/1.52  --inst_passive_queues_freq              [25;2]
% 7.60/1.52  --inst_dismatching                      true
% 7.60/1.52  --inst_eager_unprocessed_to_passive     true
% 7.60/1.52  --inst_prop_sim_given                   true
% 7.60/1.52  --inst_prop_sim_new                     false
% 7.60/1.52  --inst_subs_new                         false
% 7.60/1.52  --inst_eq_res_simp                      false
% 7.60/1.52  --inst_subs_given                       false
% 7.60/1.52  --inst_orphan_elimination               true
% 7.60/1.52  --inst_learning_loop_flag               true
% 7.60/1.52  --inst_learning_start                   3000
% 7.60/1.52  --inst_learning_factor                  2
% 7.60/1.52  --inst_start_prop_sim_after_learn       3
% 7.60/1.52  --inst_sel_renew                        solver
% 7.60/1.52  --inst_lit_activity_flag                true
% 7.60/1.52  --inst_restr_to_given                   false
% 7.60/1.52  --inst_activity_threshold               500
% 7.60/1.52  --inst_out_proof                        true
% 7.60/1.52  
% 7.60/1.52  ------ Resolution Options
% 7.60/1.52  
% 7.60/1.52  --resolution_flag                       true
% 7.60/1.52  --res_lit_sel                           adaptive
% 7.60/1.52  --res_lit_sel_side                      none
% 7.60/1.52  --res_ordering                          kbo
% 7.60/1.52  --res_to_prop_solver                    active
% 7.60/1.52  --res_prop_simpl_new                    false
% 7.60/1.52  --res_prop_simpl_given                  true
% 7.60/1.52  --res_passive_queue_type                priority_queues
% 7.60/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.60/1.52  --res_passive_queues_freq               [15;5]
% 7.60/1.52  --res_forward_subs                      full
% 7.60/1.52  --res_backward_subs                     full
% 7.60/1.52  --res_forward_subs_resolution           true
% 7.60/1.52  --res_backward_subs_resolution          true
% 7.60/1.52  --res_orphan_elimination                true
% 7.60/1.52  --res_time_limit                        2.
% 7.60/1.52  --res_out_proof                         true
% 7.60/1.52  
% 7.60/1.52  ------ Superposition Options
% 7.60/1.52  
% 7.60/1.52  --superposition_flag                    true
% 7.60/1.52  --sup_passive_queue_type                priority_queues
% 7.60/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.60/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.60/1.52  --demod_completeness_check              fast
% 7.60/1.52  --demod_use_ground                      true
% 7.60/1.52  --sup_to_prop_solver                    passive
% 7.60/1.52  --sup_prop_simpl_new                    true
% 7.60/1.52  --sup_prop_simpl_given                  true
% 7.60/1.52  --sup_fun_splitting                     true
% 7.60/1.52  --sup_smt_interval                      50000
% 7.60/1.52  
% 7.60/1.52  ------ Superposition Simplification Setup
% 7.60/1.52  
% 7.60/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.60/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.60/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.60/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.60/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.60/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.60/1.52  --sup_immed_triv                        [TrivRules]
% 7.60/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.52  --sup_immed_bw_main                     []
% 7.60/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.60/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.60/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.52  --sup_input_bw                          []
% 7.60/1.52  
% 7.60/1.52  ------ Combination Options
% 7.60/1.52  
% 7.60/1.52  --comb_res_mult                         3
% 7.60/1.52  --comb_sup_mult                         2
% 7.60/1.52  --comb_inst_mult                        10
% 7.60/1.52  
% 7.60/1.52  ------ Debug Options
% 7.60/1.52  
% 7.60/1.52  --dbg_backtrace                         false
% 7.60/1.52  --dbg_dump_prop_clauses                 false
% 7.60/1.52  --dbg_dump_prop_clauses_file            -
% 7.60/1.52  --dbg_out_stat                          false
% 7.60/1.52  ------ Parsing...
% 7.60/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.60/1.52  
% 7.60/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.60/1.52  
% 7.60/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.60/1.52  
% 7.60/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.52  ------ Proving...
% 7.60/1.52  ------ Problem Properties 
% 7.60/1.52  
% 7.60/1.52  
% 7.60/1.52  clauses                                 17
% 7.60/1.52  conjectures                             3
% 7.60/1.52  EPR                                     3
% 7.60/1.52  Horn                                    16
% 7.60/1.52  unary                                   4
% 7.60/1.52  binary                                  9
% 7.60/1.52  lits                                    34
% 7.60/1.52  lits eq                                 9
% 7.60/1.52  fd_pure                                 0
% 7.60/1.52  fd_pseudo                               0
% 7.60/1.52  fd_cond                                 0
% 7.60/1.52  fd_pseudo_cond                          1
% 7.60/1.52  AC symbols                              0
% 7.60/1.52  
% 7.60/1.52  ------ Schedule dynamic 5 is on 
% 7.60/1.52  
% 7.60/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.60/1.52  
% 7.60/1.52  
% 7.60/1.52  ------ 
% 7.60/1.52  Current options:
% 7.60/1.52  ------ 
% 7.60/1.52  
% 7.60/1.52  ------ Input Options
% 7.60/1.52  
% 7.60/1.52  --out_options                           all
% 7.60/1.52  --tptp_safe_out                         true
% 7.60/1.52  --problem_path                          ""
% 7.60/1.52  --include_path                          ""
% 7.60/1.52  --clausifier                            res/vclausify_rel
% 7.60/1.52  --clausifier_options                    ""
% 7.60/1.52  --stdin                                 false
% 7.60/1.52  --stats_out                             all
% 7.60/1.52  
% 7.60/1.52  ------ General Options
% 7.60/1.52  
% 7.60/1.52  --fof                                   false
% 7.60/1.52  --time_out_real                         305.
% 7.60/1.52  --time_out_virtual                      -1.
% 7.60/1.52  --symbol_type_check                     false
% 7.60/1.52  --clausify_out                          false
% 7.60/1.52  --sig_cnt_out                           false
% 7.60/1.52  --trig_cnt_out                          false
% 7.60/1.52  --trig_cnt_out_tolerance                1.
% 7.60/1.52  --trig_cnt_out_sk_spl                   false
% 7.60/1.52  --abstr_cl_out                          false
% 7.60/1.52  
% 7.60/1.52  ------ Global Options
% 7.60/1.52  
% 7.60/1.52  --schedule                              default
% 7.60/1.52  --add_important_lit                     false
% 7.60/1.52  --prop_solver_per_cl                    1000
% 7.60/1.52  --min_unsat_core                        false
% 7.60/1.52  --soft_assumptions                      false
% 7.60/1.52  --soft_lemma_size                       3
% 7.60/1.52  --prop_impl_unit_size                   0
% 7.60/1.52  --prop_impl_unit                        []
% 7.60/1.52  --share_sel_clauses                     true
% 7.60/1.52  --reset_solvers                         false
% 7.60/1.52  --bc_imp_inh                            [conj_cone]
% 7.60/1.52  --conj_cone_tolerance                   3.
% 7.60/1.52  --extra_neg_conj                        none
% 7.60/1.52  --large_theory_mode                     true
% 7.60/1.52  --prolific_symb_bound                   200
% 7.60/1.52  --lt_threshold                          2000
% 7.60/1.52  --clause_weak_htbl                      true
% 7.60/1.52  --gc_record_bc_elim                     false
% 7.60/1.52  
% 7.60/1.52  ------ Preprocessing Options
% 7.60/1.52  
% 7.60/1.52  --preprocessing_flag                    true
% 7.60/1.52  --time_out_prep_mult                    0.1
% 7.60/1.52  --splitting_mode                        input
% 7.60/1.52  --splitting_grd                         true
% 7.60/1.52  --splitting_cvd                         false
% 7.60/1.52  --splitting_cvd_svl                     false
% 7.60/1.52  --splitting_nvd                         32
% 7.60/1.52  --sub_typing                            true
% 7.60/1.52  --prep_gs_sim                           true
% 7.60/1.52  --prep_unflatten                        true
% 7.60/1.52  --prep_res_sim                          true
% 7.60/1.52  --prep_upred                            true
% 7.60/1.52  --prep_sem_filter                       exhaustive
% 7.60/1.52  --prep_sem_filter_out                   false
% 7.60/1.52  --pred_elim                             true
% 7.60/1.52  --res_sim_input                         true
% 7.60/1.52  --eq_ax_congr_red                       true
% 7.60/1.52  --pure_diseq_elim                       true
% 7.60/1.52  --brand_transform                       false
% 7.60/1.52  --non_eq_to_eq                          false
% 7.60/1.52  --prep_def_merge                        true
% 7.60/1.52  --prep_def_merge_prop_impl              false
% 7.60/1.52  --prep_def_merge_mbd                    true
% 7.60/1.52  --prep_def_merge_tr_red                 false
% 7.60/1.52  --prep_def_merge_tr_cl                  false
% 7.60/1.52  --smt_preprocessing                     true
% 7.60/1.52  --smt_ac_axioms                         fast
% 7.60/1.52  --preprocessed_out                      false
% 7.60/1.52  --preprocessed_stats                    false
% 7.60/1.52  
% 7.60/1.52  ------ Abstraction refinement Options
% 7.60/1.52  
% 7.60/1.52  --abstr_ref                             []
% 7.60/1.52  --abstr_ref_prep                        false
% 7.60/1.52  --abstr_ref_until_sat                   false
% 7.60/1.52  --abstr_ref_sig_restrict                funpre
% 7.60/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.60/1.52  --abstr_ref_under                       []
% 7.60/1.52  
% 7.60/1.52  ------ SAT Options
% 7.60/1.52  
% 7.60/1.52  --sat_mode                              false
% 7.60/1.52  --sat_fm_restart_options                ""
% 7.60/1.52  --sat_gr_def                            false
% 7.60/1.52  --sat_epr_types                         true
% 7.60/1.52  --sat_non_cyclic_types                  false
% 7.60/1.52  --sat_finite_models                     false
% 7.60/1.52  --sat_fm_lemmas                         false
% 7.60/1.52  --sat_fm_prep                           false
% 7.60/1.52  --sat_fm_uc_incr                        true
% 7.60/1.52  --sat_out_model                         small
% 7.60/1.52  --sat_out_clauses                       false
% 7.60/1.52  
% 7.60/1.52  ------ QBF Options
% 7.60/1.52  
% 7.60/1.52  --qbf_mode                              false
% 7.60/1.52  --qbf_elim_univ                         false
% 7.60/1.52  --qbf_dom_inst                          none
% 7.60/1.52  --qbf_dom_pre_inst                      false
% 7.60/1.52  --qbf_sk_in                             false
% 7.60/1.52  --qbf_pred_elim                         true
% 7.60/1.52  --qbf_split                             512
% 7.60/1.52  
% 7.60/1.52  ------ BMC1 Options
% 7.60/1.52  
% 7.60/1.52  --bmc1_incremental                      false
% 7.60/1.52  --bmc1_axioms                           reachable_all
% 7.60/1.52  --bmc1_min_bound                        0
% 7.60/1.52  --bmc1_max_bound                        -1
% 7.60/1.52  --bmc1_max_bound_default                -1
% 7.60/1.52  --bmc1_symbol_reachability              true
% 7.60/1.52  --bmc1_property_lemmas                  false
% 7.60/1.52  --bmc1_k_induction                      false
% 7.60/1.52  --bmc1_non_equiv_states                 false
% 7.60/1.52  --bmc1_deadlock                         false
% 7.60/1.52  --bmc1_ucm                              false
% 7.60/1.52  --bmc1_add_unsat_core                   none
% 7.60/1.52  --bmc1_unsat_core_children              false
% 7.60/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.60/1.52  --bmc1_out_stat                         full
% 7.60/1.52  --bmc1_ground_init                      false
% 7.60/1.52  --bmc1_pre_inst_next_state              false
% 7.60/1.52  --bmc1_pre_inst_state                   false
% 7.60/1.52  --bmc1_pre_inst_reach_state             false
% 7.60/1.52  --bmc1_out_unsat_core                   false
% 7.60/1.52  --bmc1_aig_witness_out                  false
% 7.60/1.52  --bmc1_verbose                          false
% 7.60/1.52  --bmc1_dump_clauses_tptp                false
% 7.60/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.60/1.52  --bmc1_dump_file                        -
% 7.60/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.60/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.60/1.52  --bmc1_ucm_extend_mode                  1
% 7.60/1.52  --bmc1_ucm_init_mode                    2
% 7.60/1.52  --bmc1_ucm_cone_mode                    none
% 7.60/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.60/1.52  --bmc1_ucm_relax_model                  4
% 7.60/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.60/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.60/1.52  --bmc1_ucm_layered_model                none
% 7.60/1.52  --bmc1_ucm_max_lemma_size               10
% 7.60/1.52  
% 7.60/1.52  ------ AIG Options
% 7.60/1.52  
% 7.60/1.52  --aig_mode                              false
% 7.60/1.52  
% 7.60/1.52  ------ Instantiation Options
% 7.60/1.52  
% 7.60/1.52  --instantiation_flag                    true
% 7.60/1.52  --inst_sos_flag                         true
% 7.60/1.52  --inst_sos_phase                        true
% 7.60/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.60/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.60/1.52  --inst_lit_sel_side                     none
% 7.60/1.52  --inst_solver_per_active                1400
% 7.60/1.52  --inst_solver_calls_frac                1.
% 7.60/1.52  --inst_passive_queue_type               priority_queues
% 7.60/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.60/1.52  --inst_passive_queues_freq              [25;2]
% 7.60/1.52  --inst_dismatching                      true
% 7.60/1.52  --inst_eager_unprocessed_to_passive     true
% 7.60/1.52  --inst_prop_sim_given                   true
% 7.60/1.52  --inst_prop_sim_new                     false
% 7.60/1.52  --inst_subs_new                         false
% 7.60/1.52  --inst_eq_res_simp                      false
% 7.60/1.52  --inst_subs_given                       false
% 7.60/1.52  --inst_orphan_elimination               true
% 7.60/1.52  --inst_learning_loop_flag               true
% 7.60/1.52  --inst_learning_start                   3000
% 7.60/1.52  --inst_learning_factor                  2
% 7.60/1.52  --inst_start_prop_sim_after_learn       3
% 7.60/1.52  --inst_sel_renew                        solver
% 7.60/1.52  --inst_lit_activity_flag                true
% 7.60/1.52  --inst_restr_to_given                   false
% 7.60/1.52  --inst_activity_threshold               500
% 7.60/1.52  --inst_out_proof                        true
% 7.60/1.52  
% 7.60/1.52  ------ Resolution Options
% 7.60/1.52  
% 7.60/1.52  --resolution_flag                       false
% 7.60/1.52  --res_lit_sel                           adaptive
% 7.60/1.52  --res_lit_sel_side                      none
% 7.60/1.52  --res_ordering                          kbo
% 7.60/1.52  --res_to_prop_solver                    active
% 7.60/1.52  --res_prop_simpl_new                    false
% 7.60/1.52  --res_prop_simpl_given                  true
% 7.60/1.52  --res_passive_queue_type                priority_queues
% 7.60/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.60/1.52  --res_passive_queues_freq               [15;5]
% 7.60/1.52  --res_forward_subs                      full
% 7.60/1.52  --res_backward_subs                     full
% 7.60/1.52  --res_forward_subs_resolution           true
% 7.60/1.52  --res_backward_subs_resolution          true
% 7.60/1.52  --res_orphan_elimination                true
% 7.60/1.52  --res_time_limit                        2.
% 7.60/1.52  --res_out_proof                         true
% 7.60/1.52  
% 7.60/1.52  ------ Superposition Options
% 7.60/1.52  
% 7.60/1.52  --superposition_flag                    true
% 7.60/1.52  --sup_passive_queue_type                priority_queues
% 7.60/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.60/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.60/1.52  --demod_completeness_check              fast
% 7.60/1.52  --demod_use_ground                      true
% 7.60/1.52  --sup_to_prop_solver                    passive
% 7.60/1.52  --sup_prop_simpl_new                    true
% 7.60/1.52  --sup_prop_simpl_given                  true
% 7.60/1.52  --sup_fun_splitting                     true
% 7.60/1.52  --sup_smt_interval                      50000
% 7.60/1.52  
% 7.60/1.52  ------ Superposition Simplification Setup
% 7.60/1.52  
% 7.60/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.60/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.60/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.60/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.60/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.60/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.60/1.52  --sup_immed_triv                        [TrivRules]
% 7.60/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.52  --sup_immed_bw_main                     []
% 7.60/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.60/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.60/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.52  --sup_input_bw                          []
% 7.60/1.52  
% 7.60/1.52  ------ Combination Options
% 7.60/1.52  
% 7.60/1.52  --comb_res_mult                         3
% 7.60/1.52  --comb_sup_mult                         2
% 7.60/1.52  --comb_inst_mult                        10
% 7.60/1.52  
% 7.60/1.52  ------ Debug Options
% 7.60/1.52  
% 7.60/1.52  --dbg_backtrace                         false
% 7.60/1.52  --dbg_dump_prop_clauses                 false
% 7.60/1.52  --dbg_dump_prop_clauses_file            -
% 7.60/1.52  --dbg_out_stat                          false
% 7.60/1.52  
% 7.60/1.52  
% 7.60/1.52  
% 7.60/1.52  
% 7.60/1.52  ------ Proving...
% 7.60/1.52  
% 7.60/1.52  
% 7.60/1.52  % SZS status Theorem for theBenchmark.p
% 7.60/1.52  
% 7.60/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.60/1.52  
% 7.60/1.52  fof(f15,conjecture,(
% 7.60/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f16,negated_conjecture,(
% 7.60/1.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.60/1.52    inference(negated_conjecture,[],[f15])).
% 7.60/1.52  
% 7.60/1.52  fof(f29,plain,(
% 7.60/1.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.60/1.52    inference(ennf_transformation,[],[f16])).
% 7.60/1.52  
% 7.60/1.52  fof(f30,plain,(
% 7.60/1.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.60/1.52    inference(flattening,[],[f29])).
% 7.60/1.52  
% 7.60/1.52  fof(f34,plain,(
% 7.60/1.52    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.60/1.52    inference(nnf_transformation,[],[f30])).
% 7.60/1.52  
% 7.60/1.52  fof(f35,plain,(
% 7.60/1.52    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.60/1.52    inference(flattening,[],[f34])).
% 7.60/1.52  
% 7.60/1.52  fof(f37,plain,(
% 7.60/1.52    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.60/1.52    introduced(choice_axiom,[])).
% 7.60/1.52  
% 7.60/1.52  fof(f36,plain,(
% 7.60/1.52    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.60/1.52    introduced(choice_axiom,[])).
% 7.60/1.52  
% 7.60/1.52  fof(f38,plain,(
% 7.60/1.52    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.60/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 7.60/1.52  
% 7.60/1.52  fof(f58,plain,(
% 7.60/1.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.60/1.52    inference(cnf_transformation,[],[f38])).
% 7.60/1.52  
% 7.60/1.52  fof(f10,axiom,(
% 7.60/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f33,plain,(
% 7.60/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.60/1.52    inference(nnf_transformation,[],[f10])).
% 7.60/1.52  
% 7.60/1.52  fof(f50,plain,(
% 7.60/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.60/1.52    inference(cnf_transformation,[],[f33])).
% 7.60/1.52  
% 7.60/1.52  fof(f2,axiom,(
% 7.60/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f31,plain,(
% 7.60/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.60/1.52    inference(nnf_transformation,[],[f2])).
% 7.60/1.52  
% 7.60/1.52  fof(f32,plain,(
% 7.60/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.60/1.52    inference(flattening,[],[f31])).
% 7.60/1.52  
% 7.60/1.52  fof(f40,plain,(
% 7.60/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.60/1.52    inference(cnf_transformation,[],[f32])).
% 7.60/1.52  
% 7.60/1.52  fof(f65,plain,(
% 7.60/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.60/1.52    inference(equality_resolution,[],[f40])).
% 7.60/1.52  
% 7.60/1.52  fof(f8,axiom,(
% 7.60/1.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f22,plain,(
% 7.60/1.52    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.60/1.52    inference(ennf_transformation,[],[f8])).
% 7.60/1.52  
% 7.60/1.52  fof(f48,plain,(
% 7.60/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.60/1.52    inference(cnf_transformation,[],[f22])).
% 7.60/1.52  
% 7.60/1.52  fof(f3,axiom,(
% 7.60/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f43,plain,(
% 7.60/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.60/1.52    inference(cnf_transformation,[],[f3])).
% 7.60/1.52  
% 7.60/1.52  fof(f9,axiom,(
% 7.60/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f49,plain,(
% 7.60/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.60/1.52    inference(cnf_transformation,[],[f9])).
% 7.60/1.52  
% 7.60/1.52  fof(f61,plain,(
% 7.60/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.60/1.52    inference(definition_unfolding,[],[f43,f49])).
% 7.60/1.52  
% 7.60/1.52  fof(f63,plain,(
% 7.60/1.52    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.60/1.52    inference(definition_unfolding,[],[f48,f61])).
% 7.60/1.52  
% 7.60/1.52  fof(f51,plain,(
% 7.60/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f33])).
% 7.60/1.52  
% 7.60/1.52  fof(f59,plain,(
% 7.60/1.52    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.60/1.52    inference(cnf_transformation,[],[f38])).
% 7.60/1.52  
% 7.60/1.52  fof(f14,axiom,(
% 7.60/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f27,plain,(
% 7.60/1.52    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.60/1.52    inference(ennf_transformation,[],[f14])).
% 7.60/1.52  
% 7.60/1.52  fof(f28,plain,(
% 7.60/1.52    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.60/1.52    inference(flattening,[],[f27])).
% 7.60/1.52  
% 7.60/1.52  fof(f55,plain,(
% 7.60/1.52    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f28])).
% 7.60/1.52  
% 7.60/1.52  fof(f57,plain,(
% 7.60/1.52    l1_pre_topc(sK0)),
% 7.60/1.52    inference(cnf_transformation,[],[f38])).
% 7.60/1.52  
% 7.60/1.52  fof(f5,axiom,(
% 7.60/1.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f18,plain,(
% 7.60/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.60/1.52    inference(ennf_transformation,[],[f5])).
% 7.60/1.52  
% 7.60/1.52  fof(f19,plain,(
% 7.60/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.60/1.52    inference(flattening,[],[f18])).
% 7.60/1.52  
% 7.60/1.52  fof(f45,plain,(
% 7.60/1.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f19])).
% 7.60/1.52  
% 7.60/1.52  fof(f7,axiom,(
% 7.60/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f20,plain,(
% 7.60/1.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.60/1.52    inference(ennf_transformation,[],[f7])).
% 7.60/1.52  
% 7.60/1.52  fof(f21,plain,(
% 7.60/1.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.60/1.52    inference(flattening,[],[f20])).
% 7.60/1.52  
% 7.60/1.52  fof(f47,plain,(
% 7.60/1.52    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.60/1.52    inference(cnf_transformation,[],[f21])).
% 7.60/1.52  
% 7.60/1.52  fof(f13,axiom,(
% 7.60/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f26,plain,(
% 7.60/1.52    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.60/1.52    inference(ennf_transformation,[],[f13])).
% 7.60/1.52  
% 7.60/1.52  fof(f54,plain,(
% 7.60/1.52    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f26])).
% 7.60/1.52  
% 7.60/1.52  fof(f1,axiom,(
% 7.60/1.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f39,plain,(
% 7.60/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f1])).
% 7.60/1.52  
% 7.60/1.52  fof(f4,axiom,(
% 7.60/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f17,plain,(
% 7.60/1.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.60/1.52    inference(ennf_transformation,[],[f4])).
% 7.60/1.52  
% 7.60/1.52  fof(f44,plain,(
% 7.60/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f17])).
% 7.60/1.52  
% 7.60/1.52  fof(f6,axiom,(
% 7.60/1.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f46,plain,(
% 7.60/1.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f6])).
% 7.60/1.52  
% 7.60/1.52  fof(f62,plain,(
% 7.60/1.52    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 7.60/1.52    inference(definition_unfolding,[],[f46,f61])).
% 7.60/1.52  
% 7.60/1.52  fof(f12,axiom,(
% 7.60/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f25,plain,(
% 7.60/1.52    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.60/1.52    inference(ennf_transformation,[],[f12])).
% 7.60/1.52  
% 7.60/1.52  fof(f53,plain,(
% 7.60/1.52    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f25])).
% 7.60/1.52  
% 7.60/1.52  fof(f11,axiom,(
% 7.60/1.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 7.60/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.52  
% 7.60/1.52  fof(f23,plain,(
% 7.60/1.52    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.60/1.52    inference(ennf_transformation,[],[f11])).
% 7.60/1.52  
% 7.60/1.52  fof(f24,plain,(
% 7.60/1.52    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.60/1.52    inference(flattening,[],[f23])).
% 7.60/1.52  
% 7.60/1.52  fof(f52,plain,(
% 7.60/1.52    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f24])).
% 7.60/1.52  
% 7.60/1.52  fof(f56,plain,(
% 7.60/1.52    v2_pre_topc(sK0)),
% 7.60/1.52    inference(cnf_transformation,[],[f38])).
% 7.60/1.52  
% 7.60/1.52  fof(f42,plain,(
% 7.60/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.60/1.52    inference(cnf_transformation,[],[f32])).
% 7.60/1.52  
% 7.60/1.52  fof(f60,plain,(
% 7.60/1.52    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.60/1.52    inference(cnf_transformation,[],[f38])).
% 7.60/1.52  
% 7.60/1.52  cnf(c_17,negated_conjecture,
% 7.60/1.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.60/1.52      inference(cnf_transformation,[],[f58]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1300,plain,
% 7.60/1.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_10,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.60/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1303,plain,
% 7.60/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.60/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2365,plain,
% 7.60/1.52      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1300,c_1303]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_3,plain,
% 7.60/1.52      ( r1_tarski(X0,X0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1308,plain,
% 7.60/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_8,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.60/1.52      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 7.60/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_9,plain,
% 7.60/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.60/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_147,plain,
% 7.60/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.60/1.52      inference(prop_impl,[status(thm)],[c_9]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_148,plain,
% 7.60/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.60/1.52      inference(renaming,[status(thm)],[c_147]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_186,plain,
% 7.60/1.52      ( ~ r1_tarski(X0,X1)
% 7.60/1.52      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 7.60/1.52      inference(bin_hyper_res,[status(thm)],[c_8,c_148]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1299,plain,
% 7.60/1.52      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 7.60/1.52      | r1_tarski(X0,X2) != iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2368,plain,
% 7.60/1.52      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1308,c_1299]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2372,plain,
% 7.60/1.52      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 7.60/1.52      | r1_tarski(X0,X2) != iProver_top ),
% 7.60/1.52      inference(demodulation,[status(thm)],[c_2368,c_1299]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_3782,plain,
% 7.60/1.52      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_2365,c_2372]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_16,negated_conjecture,
% 7.60/1.52      ( v4_pre_topc(sK1,sK0)
% 7.60/1.52      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.60/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1301,plain,
% 7.60/1.52      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.60/1.52      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_4068,plain,
% 7.60/1.52      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.60/1.52      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.60/1.52      inference(demodulation,[status(thm)],[c_3782,c_1301]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_14,plain,
% 7.60/1.52      ( ~ v4_pre_topc(X0,X1)
% 7.60/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.60/1.52      | r1_tarski(k2_tops_1(X1,X0),X0)
% 7.60/1.52      | ~ l1_pre_topc(X1) ),
% 7.60/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_18,negated_conjecture,
% 7.60/1.52      ( l1_pre_topc(sK0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_286,plain,
% 7.60/1.52      ( ~ v4_pre_topc(X0,X1)
% 7.60/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.60/1.52      | r1_tarski(k2_tops_1(X1,X0),X0)
% 7.60/1.52      | sK0 != X1 ),
% 7.60/1.52      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_287,plain,
% 7.60/1.52      ( ~ v4_pre_topc(X0,sK0)
% 7.60/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.60/1.52      | r1_tarski(k2_tops_1(sK0,X0),X0) ),
% 7.60/1.52      inference(unflattening,[status(thm)],[c_286]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1297,plain,
% 7.60/1.52      ( v4_pre_topc(X0,sK0) != iProver_top
% 7.60/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.60/1.52      | r1_tarski(k2_tops_1(sK0,X0),X0) = iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1751,plain,
% 7.60/1.52      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.60/1.52      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1300,c_1297]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_5,plain,
% 7.60/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.60/1.52      inference(cnf_transformation,[],[f45]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1306,plain,
% 7.60/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.60/1.52      | r1_tarski(X1,X2) != iProver_top
% 7.60/1.52      | r1_tarski(X0,X2) = iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2550,plain,
% 7.60/1.52      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.60/1.52      | r1_tarski(k2_tops_1(sK0,sK1),X0) = iProver_top
% 7.60/1.52      | r1_tarski(sK1,X0) != iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1751,c_1306]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2992,plain,
% 7.60/1.52      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.60/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.60/1.52      | r1_tarski(k2_tops_1(sK0,sK1),X1) = iProver_top
% 7.60/1.52      | r1_tarski(sK1,X0) != iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_2550,c_1306]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_4385,plain,
% 7.60/1.52      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.60/1.52      | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 7.60/1.52      | r1_tarski(sK1,sK1) != iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_2365,c_2992]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2567,plain,
% 7.60/1.52      ( r1_tarski(sK1,sK1) ),
% 7.60/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2568,plain,
% 7.60/1.52      ( r1_tarski(sK1,sK1) = iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_2567]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_4773,plain,
% 7.60/1.52      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 7.60/1.52      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.60/1.52      inference(global_propositional_subsumption,
% 7.60/1.52                [status(thm)],
% 7.60/1.52                [c_4385,c_2568]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_4774,plain,
% 7.60/1.52      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.60/1.52      | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 7.60/1.52      inference(renaming,[status(thm)],[c_4773]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_7,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.60/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.60/1.52      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f47]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_185,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.60/1.52      | ~ r1_tarski(X2,X1)
% 7.60/1.52      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.60/1.52      inference(bin_hyper_res,[status(thm)],[c_7,c_148]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_610,plain,
% 7.60/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.60/1.52      inference(prop_impl,[status(thm)],[c_9]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_611,plain,
% 7.60/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.60/1.52      inference(renaming,[status(thm)],[c_610]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_646,plain,
% 7.60/1.52      ( ~ r1_tarski(X0,X1)
% 7.60/1.52      | ~ r1_tarski(X2,X1)
% 7.60/1.52      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.60/1.52      inference(bin_hyper_res,[status(thm)],[c_185,c_611]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1294,plain,
% 7.60/1.52      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 7.60/1.52      | r1_tarski(X1,X0) != iProver_top
% 7.60/1.52      | r1_tarski(X2,X0) != iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_15718,plain,
% 7.60/1.52      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 7.60/1.52      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_2365,c_1294]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_16125,plain,
% 7.60/1.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
% 7.60/1.52      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_4774,c_15718]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_13,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.60/1.52      | ~ l1_pre_topc(X1)
% 7.60/1.52      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_301,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.60/1.52      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 7.60/1.52      | sK0 != X1 ),
% 7.60/1.52      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_302,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.60/1.52      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 7.60/1.52      inference(unflattening,[status(thm)],[c_301]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1296,plain,
% 7.60/1.52      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 7.60/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1547,plain,
% 7.60/1.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1300,c_1296]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_0,plain,
% 7.60/1.52      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f39]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_4,plain,
% 7.60/1.52      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.60/1.52      inference(cnf_transformation,[],[f44]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1307,plain,
% 7.60/1.52      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2057,plain,
% 7.60/1.52      ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1
% 7.60/1.52      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1751,c_1307]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2060,plain,
% 7.60/1.52      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.60/1.52      | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1301,c_2057]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_4081,plain,
% 7.60/1.52      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.60/1.52      | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_3782,c_2060]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_6,plain,
% 7.60/1.52      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1305,plain,
% 7.60/1.52      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1944,plain,
% 7.60/1.52      ( k2_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = X0 ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1305,c_1307]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_3075,plain,
% 7.60/1.52      ( k2_xboole_0(k7_subset_1(X0,X0,X1),X0) = X0 ),
% 7.60/1.52      inference(demodulation,[status(thm)],[c_2368,c_1944]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_9019,plain,
% 7.60/1.52      ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_4081,c_3075]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_9499,plain,
% 7.60/1.52      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_0,c_9019]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_16137,plain,
% 7.60/1.52      ( k2_pre_topc(sK0,sK1) = sK1
% 7.60/1.52      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.60/1.52      inference(light_normalisation,
% 7.60/1.52                [status(thm)],
% 7.60/1.52                [c_16125,c_1547,c_9499]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_16163,plain,
% 7.60/1.52      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.60/1.52      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_4068,c_16137]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2549,plain,
% 7.60/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.60/1.52      | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))),X1) = iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1305,c_1306]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2551,plain,
% 7.60/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.60/1.52      | r1_tarski(k7_subset_1(X0,X0,X2),X1) = iProver_top ),
% 7.60/1.52      inference(demodulation,[status(thm)],[c_2549,c_2368]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_16122,plain,
% 7.60/1.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(X0,X0,X1)) = k2_xboole_0(sK1,k7_subset_1(X0,X0,X1))
% 7.60/1.52      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_2551,c_15718]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_17805,plain,
% 7.60/1.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X0)) = k2_xboole_0(sK1,k7_subset_1(sK1,sK1,X0)) ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_2365,c_16122]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_2284,plain,
% 7.60/1.52      ( k2_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_0,c_1944]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_3074,plain,
% 7.60/1.52      ( k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0 ),
% 7.60/1.52      inference(demodulation,[status(thm)],[c_2368,c_2284]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_17832,plain,
% 7.60/1.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X0)) = sK1 ),
% 7.60/1.52      inference(demodulation,[status(thm)],[c_17805,c_3074]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_18063,plain,
% 7.60/1.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = sK1
% 7.60/1.52      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_16163,c_17832]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_18064,plain,
% 7.60/1.52      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.60/1.52      inference(demodulation,[status(thm)],[c_18063,c_1547]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_12,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.60/1.52      | ~ l1_pre_topc(X1)
% 7.60/1.52      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f53]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_313,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.60/1.52      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 7.60/1.52      | sK0 != X1 ),
% 7.60/1.52      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_314,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.60/1.52      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 7.60/1.52      inference(unflattening,[status(thm)],[c_313]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1295,plain,
% 7.60/1.52      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 7.60/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.60/1.52      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1689,plain,
% 7.60/1.52      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.60/1.52      inference(superposition,[status(thm)],[c_1300,c_1295]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_18066,plain,
% 7.60/1.52      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.60/1.52      inference(demodulation,[status(thm)],[c_18064,c_1689]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_876,plain,( X0 = X0 ),theory(equality) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1846,plain,
% 7.60/1.52      ( sK1 = sK1 ),
% 7.60/1.52      inference(instantiation,[status(thm)],[c_876]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_877,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1382,plain,
% 7.60/1.52      ( k2_pre_topc(sK0,sK1) != X0
% 7.60/1.52      | sK1 != X0
% 7.60/1.52      | sK1 = k2_pre_topc(sK0,sK1) ),
% 7.60/1.52      inference(instantiation,[status(thm)],[c_877]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1518,plain,
% 7.60/1.52      ( k2_pre_topc(sK0,sK1) != sK1
% 7.60/1.52      | sK1 = k2_pre_topc(sK0,sK1)
% 7.60/1.52      | sK1 != sK1 ),
% 7.60/1.52      inference(instantiation,[status(thm)],[c_1382]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_886,plain,
% 7.60/1.52      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.60/1.52      theory(equality) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1333,plain,
% 7.60/1.52      ( ~ v4_pre_topc(X0,X1)
% 7.60/1.52      | v4_pre_topc(sK1,sK0)
% 7.60/1.52      | sK1 != X0
% 7.60/1.52      | sK0 != X1 ),
% 7.60/1.52      inference(instantiation,[status(thm)],[c_886]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1369,plain,
% 7.60/1.52      ( ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 7.60/1.52      | v4_pre_topc(sK1,sK0)
% 7.60/1.52      | sK1 != k2_pre_topc(sK0,sK1)
% 7.60/1.52      | sK0 != sK0 ),
% 7.60/1.52      inference(instantiation,[status(thm)],[c_1333]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_11,plain,
% 7.60/1.52      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 7.60/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.60/1.52      | ~ v2_pre_topc(X0)
% 7.60/1.52      | ~ l1_pre_topc(X0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_19,negated_conjecture,
% 7.60/1.52      ( v2_pre_topc(sK0) ),
% 7.60/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_265,plain,
% 7.60/1.52      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 7.60/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.60/1.52      | ~ l1_pre_topc(X0)
% 7.60/1.52      | sK0 != X0 ),
% 7.60/1.52      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_266,plain,
% 7.60/1.52      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 7.60/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.60/1.52      | ~ l1_pre_topc(sK0) ),
% 7.60/1.52      inference(unflattening,[status(thm)],[c_265]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_270,plain,
% 7.60/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.60/1.52      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 7.60/1.52      inference(global_propositional_subsumption,
% 7.60/1.52                [status(thm)],
% 7.60/1.52                [c_266,c_18]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_271,plain,
% 7.60/1.52      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 7.60/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.60/1.52      inference(renaming,[status(thm)],[c_270]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_518,plain,
% 7.60/1.52      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 7.60/1.52      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 7.60/1.52      | sK1 != X0 ),
% 7.60/1.52      inference(resolution_lifted,[status(thm)],[c_17,c_271]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_519,plain,
% 7.60/1.52      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
% 7.60/1.52      inference(unflattening,[status(thm)],[c_518]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_1,plain,
% 7.60/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.60/1.52      inference(cnf_transformation,[],[f42]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_61,plain,
% 7.60/1.52      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.60/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_57,plain,
% 7.60/1.52      ( r1_tarski(sK0,sK0) ),
% 7.60/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(c_15,negated_conjecture,
% 7.60/1.52      ( ~ v4_pre_topc(sK1,sK0)
% 7.60/1.52      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.60/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.60/1.52  
% 7.60/1.52  cnf(contradiction,plain,
% 7.60/1.52      ( $false ),
% 7.60/1.52      inference(minisat,
% 7.60/1.52                [status(thm)],
% 7.60/1.52                [c_18066,c_18064,c_1846,c_1518,c_1369,c_519,c_61,c_57,
% 7.60/1.52                 c_15]) ).
% 7.60/1.52  
% 7.60/1.52  
% 7.60/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.60/1.52  
% 7.60/1.52  ------                               Statistics
% 7.60/1.52  
% 7.60/1.52  ------ General
% 7.60/1.52  
% 7.60/1.52  abstr_ref_over_cycles:                  0
% 7.60/1.52  abstr_ref_under_cycles:                 0
% 7.60/1.52  gc_basic_clause_elim:                   0
% 7.60/1.52  forced_gc_time:                         0
% 7.60/1.52  parsing_time:                           0.011
% 7.60/1.52  unif_index_cands_time:                  0.
% 7.60/1.52  unif_index_add_time:                    0.
% 7.60/1.52  orderings_time:                         0.
% 7.60/1.52  out_proof_time:                         0.01
% 7.60/1.52  total_time:                             0.583
% 7.60/1.52  num_of_symbols:                         49
% 7.60/1.52  num_of_terms:                           16630
% 7.60/1.52  
% 7.60/1.52  ------ Preprocessing
% 7.60/1.52  
% 7.60/1.52  num_of_splits:                          0
% 7.60/1.52  num_of_split_atoms:                     0
% 7.60/1.52  num_of_reused_defs:                     0
% 7.60/1.52  num_eq_ax_congr_red:                    25
% 7.60/1.52  num_of_sem_filtered_clauses:            1
% 7.60/1.52  num_of_subtypes:                        0
% 7.60/1.52  monotx_restored_types:                  0
% 7.60/1.52  sat_num_of_epr_types:                   0
% 7.60/1.52  sat_num_of_non_cyclic_types:            0
% 7.60/1.52  sat_guarded_non_collapsed_types:        0
% 7.60/1.52  num_pure_diseq_elim:                    0
% 7.60/1.52  simp_replaced_by:                       0
% 7.60/1.52  res_preprocessed:                       99
% 7.60/1.52  prep_upred:                             0
% 7.60/1.52  prep_unflattend:                        27
% 7.60/1.52  smt_new_axioms:                         0
% 7.60/1.52  pred_elim_cands:                        3
% 7.60/1.52  pred_elim:                              2
% 7.60/1.52  pred_elim_cl:                           2
% 7.60/1.52  pred_elim_cycles:                       6
% 7.60/1.52  merged_defs:                            16
% 7.60/1.52  merged_defs_ncl:                        0
% 7.60/1.52  bin_hyper_res:                          19
% 7.60/1.52  prep_cycles:                            4
% 7.60/1.52  pred_elim_time:                         0.008
% 7.60/1.52  splitting_time:                         0.
% 7.60/1.52  sem_filter_time:                        0.
% 7.60/1.52  monotx_time:                            0.001
% 7.60/1.52  subtype_inf_time:                       0.
% 7.60/1.52  
% 7.60/1.52  ------ Problem properties
% 7.60/1.52  
% 7.60/1.52  clauses:                                17
% 7.60/1.52  conjectures:                            3
% 7.60/1.52  epr:                                    3
% 7.60/1.52  horn:                                   16
% 7.60/1.52  ground:                                 3
% 7.60/1.52  unary:                                  4
% 7.60/1.52  binary:                                 9
% 7.60/1.52  lits:                                   34
% 7.60/1.52  lits_eq:                                9
% 7.60/1.52  fd_pure:                                0
% 7.60/1.52  fd_pseudo:                              0
% 7.60/1.52  fd_cond:                                0
% 7.60/1.52  fd_pseudo_cond:                         1
% 7.60/1.52  ac_symbols:                             0
% 7.60/1.52  
% 7.60/1.52  ------ Propositional Solver
% 7.60/1.52  
% 7.60/1.52  prop_solver_calls:                      32
% 7.60/1.52  prop_fast_solver_calls:                 1131
% 7.60/1.52  smt_solver_calls:                       0
% 7.60/1.52  smt_fast_solver_calls:                  0
% 7.60/1.52  prop_num_of_clauses:                    8742
% 7.60/1.52  prop_preprocess_simplified:             15941
% 7.60/1.52  prop_fo_subsumed:                       20
% 7.60/1.52  prop_solver_time:                       0.
% 7.60/1.52  smt_solver_time:                        0.
% 7.60/1.52  smt_fast_solver_time:                   0.
% 7.60/1.52  prop_fast_solver_time:                  0.
% 7.60/1.52  prop_unsat_core_time:                   0.001
% 7.60/1.52  
% 7.60/1.52  ------ QBF
% 7.60/1.52  
% 7.60/1.52  qbf_q_res:                              0
% 7.60/1.52  qbf_num_tautologies:                    0
% 7.60/1.52  qbf_prep_cycles:                        0
% 7.60/1.52  
% 7.60/1.52  ------ BMC1
% 7.60/1.52  
% 7.60/1.52  bmc1_current_bound:                     -1
% 7.60/1.52  bmc1_last_solved_bound:                 -1
% 7.60/1.52  bmc1_unsat_core_size:                   -1
% 7.60/1.52  bmc1_unsat_core_parents_size:           -1
% 7.60/1.52  bmc1_merge_next_fun:                    0
% 7.60/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.60/1.52  
% 7.60/1.52  ------ Instantiation
% 7.60/1.52  
% 7.60/1.52  inst_num_of_clauses:                    2393
% 7.60/1.52  inst_num_in_passive:                    346
% 7.60/1.52  inst_num_in_active:                     1018
% 7.60/1.52  inst_num_in_unprocessed:                1029
% 7.60/1.52  inst_num_of_loops:                      1050
% 7.60/1.52  inst_num_of_learning_restarts:          0
% 7.60/1.52  inst_num_moves_active_passive:          28
% 7.60/1.52  inst_lit_activity:                      0
% 7.60/1.52  inst_lit_activity_moves:                0
% 7.60/1.52  inst_num_tautologies:                   0
% 7.60/1.52  inst_num_prop_implied:                  0
% 7.60/1.52  inst_num_existing_simplified:           0
% 7.60/1.52  inst_num_eq_res_simplified:             0
% 7.60/1.52  inst_num_child_elim:                    0
% 7.60/1.52  inst_num_of_dismatching_blockings:      1023
% 7.60/1.52  inst_num_of_non_proper_insts:           3362
% 7.60/1.52  inst_num_of_duplicates:                 0
% 7.60/1.52  inst_inst_num_from_inst_to_res:         0
% 7.60/1.52  inst_dismatching_checking_time:         0.
% 7.60/1.52  
% 7.60/1.52  ------ Resolution
% 7.60/1.52  
% 7.60/1.52  res_num_of_clauses:                     0
% 7.60/1.52  res_num_in_passive:                     0
% 7.60/1.52  res_num_in_active:                      0
% 7.60/1.52  res_num_of_loops:                       103
% 7.60/1.52  res_forward_subset_subsumed:            204
% 7.60/1.52  res_backward_subset_subsumed:           0
% 7.60/1.52  res_forward_subsumed:                   0
% 7.60/1.52  res_backward_subsumed:                  0
% 7.60/1.52  res_forward_subsumption_resolution:     0
% 7.60/1.52  res_backward_subsumption_resolution:    0
% 7.60/1.52  res_clause_to_clause_subsumption:       4419
% 7.60/1.52  res_orphan_elimination:                 0
% 7.60/1.52  res_tautology_del:                      467
% 7.60/1.52  res_num_eq_res_simplified:              0
% 7.60/1.52  res_num_sel_changes:                    0
% 7.60/1.52  res_moves_from_active_to_pass:          0
% 7.60/1.52  
% 7.60/1.52  ------ Superposition
% 7.60/1.52  
% 7.60/1.52  sup_time_total:                         0.
% 7.60/1.52  sup_time_generating:                    0.
% 7.60/1.52  sup_time_sim_full:                      0.
% 7.60/1.52  sup_time_sim_immed:                     0.
% 7.60/1.52  
% 7.60/1.52  sup_num_of_clauses:                     618
% 7.60/1.52  sup_num_in_active:                      190
% 7.60/1.52  sup_num_in_passive:                     428
% 7.60/1.52  sup_num_of_loops:                       209
% 7.60/1.52  sup_fw_superposition:                   629
% 7.60/1.52  sup_bw_superposition:                   482
% 7.60/1.52  sup_immediate_simplified:               248
% 7.60/1.52  sup_given_eliminated:                   1
% 7.60/1.52  comparisons_done:                       0
% 7.60/1.52  comparisons_avoided:                    81
% 7.60/1.52  
% 7.60/1.52  ------ Simplifications
% 7.60/1.52  
% 7.60/1.52  
% 7.60/1.52  sim_fw_subset_subsumed:                 81
% 7.60/1.52  sim_bw_subset_subsumed:                 68
% 7.60/1.52  sim_fw_subsumed:                        20
% 7.60/1.52  sim_bw_subsumed:                        5
% 7.60/1.52  sim_fw_subsumption_res:                 0
% 7.60/1.52  sim_bw_subsumption_res:                 0
% 7.60/1.52  sim_tautology_del:                      2
% 7.60/1.52  sim_eq_tautology_del:                   22
% 7.60/1.52  sim_eq_res_simp:                        0
% 7.60/1.52  sim_fw_demodulated:                     131
% 7.60/1.52  sim_bw_demodulated:                     13
% 7.60/1.52  sim_light_normalised:                   21
% 7.60/1.52  sim_joinable_taut:                      0
% 7.60/1.52  sim_joinable_simp:                      0
% 7.60/1.52  sim_ac_normalised:                      0
% 7.60/1.52  sim_smt_subsumption:                    0
% 7.60/1.52  
%------------------------------------------------------------------------------
