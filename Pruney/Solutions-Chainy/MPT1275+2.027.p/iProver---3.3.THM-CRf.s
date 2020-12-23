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
% DateTime   : Thu Dec  3 12:15:27 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  176 (2563 expanded)
%              Number of clauses        :  107 ( 718 expanded)
%              Number of leaves         :   18 ( 541 expanded)
%              Depth                    :   26
%              Number of atoms          :  514 (12818 expanded)
%              Number of equality atoms :  186 (3478 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k2_tops_1(X0,sK1) != sK1
          | ~ v3_tops_1(sK1,X0) )
        & ( k2_tops_1(X0,sK1) = sK1
          | v3_tops_1(sK1,X0) )
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( k2_tops_1(sK0,sK1) != sK1
      | ~ v3_tops_1(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = sK1
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_tops_1(X0,X1) != k1_xboole_0 )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_tops_1(X0,X1) != k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_xboole_0
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f67])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1570,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1571,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1882,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_1571])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_172,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_173,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_172])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_173])).

cnf(c_1567,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_3300,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_1882,c_1567])).

cnf(c_11,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_402,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_403,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_357,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_358,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_tops_1(sK0,X0))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_403,c_358])).

cnf(c_467,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_850,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_20,c_467])).

cnf(c_1559,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_70,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_71,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_74,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_176,plain,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_337,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(sK0,sK1) = sK1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_176])).

cnf(c_338,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_340,plain,
    ( v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_21,c_20])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_tops_1(sK0,X0))
    | k2_tops_1(sK0,sK1) = sK1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_340,c_358])).

cnf(c_506,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_20])).

cnf(c_510,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_1140,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1702,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_tops_1(sK0,X2))
    | X2 != X0
    | k2_tops_1(sK0,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1703,plain,
    ( X0 != X1
    | k2_tops_1(sK0,X0) != X2
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1702])).

cnf(c_1705,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | sK1 != sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_1801,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_70,c_71,c_74,c_510,c_1705])).

cnf(c_1572,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_372,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_373,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_12,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_387,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_388,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_373,c_388])).

cnf(c_1563,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_1888,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1563])).

cnf(c_2202,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_1888])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_480,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_482,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_2289,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_23,c_70,c_71,c_74,c_482,c_510,c_1705])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_1566,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_1698,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_1566])).

cnf(c_2293,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2289,c_1698])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_173])).

cnf(c_1569,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_3197,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_xboole_0))) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2293,c_1569])).

cnf(c_3587,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3300,c_3197])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1565,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_1718,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1570,c_1565])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_314,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_316,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_21,c_20])).

cnf(c_1719,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1718,c_316])).

cnf(c_2292,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2289,c_1719])).

cnf(c_3590,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3587,c_2292])).

cnf(c_3632,plain,
    ( r1_tarski(sK1,k3_subset_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3590,c_1801])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_210,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_173])).

cnf(c_1568,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_2718,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1571])).

cnf(c_1574,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3104,plain,
    ( k3_subset_1(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,k3_subset_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2718,c_1574])).

cnf(c_4001,plain,
    ( k3_subset_1(sK1,k1_xboole_0) = sK1
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_3104])).

cnf(c_16,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_299,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_300,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_302,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_21,c_20])).

cnf(c_17,negated_conjecture,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_174,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_325,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(resolution,[status(thm)],[c_302,c_174])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
    | k2_tops_1(sK0,sK1) != sK1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_373])).

cnf(c_531,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_533,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_20])).

cnf(c_846,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_20,c_531])).

cnf(c_1561,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_535,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_2403,plain,
    ( k2_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1561,c_70,c_71,c_74,c_510,c_535,c_1705])).

cnf(c_3631,plain,
    ( k3_subset_1(sK1,k1_xboole_0) != sK1 ),
    inference(demodulation,[status(thm)],[c_3590,c_2403])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4001,c_3631,c_2293])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:18:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.59/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.99  
% 2.59/0.99  ------  iProver source info
% 2.59/0.99  
% 2.59/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.99  git: non_committed_changes: false
% 2.59/0.99  git: last_make_outside_of_git: false
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     num_symb
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       true
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  ------ Parsing...
% 2.59/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.99  ------ Proving...
% 2.59/0.99  ------ Problem Properties 
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  clauses                                 17
% 2.59/0.99  conjectures                             1
% 2.59/0.99  EPR                                     2
% 2.59/0.99  Horn                                    16
% 2.59/0.99  unary                                   3
% 2.59/0.99  binary                                  11
% 2.59/0.99  lits                                    34
% 2.59/0.99  lits eq                                 11
% 2.59/0.99  fd_pure                                 0
% 2.59/0.99  fd_pseudo                               0
% 2.59/0.99  fd_cond                                 0
% 2.59/0.99  fd_pseudo_cond                          1
% 2.59/0.99  AC symbols                              0
% 2.59/0.99  
% 2.59/0.99  ------ Schedule dynamic 5 is on 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  Current options:
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     none
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       false
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ Proving...
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  % SZS status Theorem for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  fof(f15,conjecture,(
% 2.59/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f16,negated_conjecture,(
% 2.59/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.59/0.99    inference(negated_conjecture,[],[f15])).
% 2.59/0.99  
% 2.59/0.99  fof(f31,plain,(
% 2.59/0.99    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f16])).
% 2.59/0.99  
% 2.59/0.99  fof(f32,plain,(
% 2.59/0.99    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.59/0.99    inference(flattening,[],[f31])).
% 2.59/0.99  
% 2.59/0.99  fof(f38,plain,(
% 2.59/0.99    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.59/0.99    inference(nnf_transformation,[],[f32])).
% 2.59/0.99  
% 2.59/0.99  fof(f39,plain,(
% 2.59/0.99    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.59/0.99    inference(flattening,[],[f38])).
% 2.59/0.99  
% 2.59/0.99  fof(f41,plain,(
% 2.59/0.99    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK1) != sK1 | ~v3_tops_1(sK1,X0)) & (k2_tops_1(X0,sK1) = sK1 | v3_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f40,plain,(
% 2.59/0.99    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f42,plain,(
% 2.59/0.99    ((k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)) & (k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 2.59/0.99  
% 2.59/0.99  fof(f63,plain,(
% 2.59/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.59/0.99    inference(cnf_transformation,[],[f42])).
% 2.59/0.99  
% 2.59/0.99  fof(f7,axiom,(
% 2.59/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f35,plain,(
% 2.59/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.59/0.99    inference(nnf_transformation,[],[f7])).
% 2.59/0.99  
% 2.59/0.99  fof(f51,plain,(
% 2.59/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f35])).
% 2.59/0.99  
% 2.59/0.99  fof(f5,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f20,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.99    inference(ennf_transformation,[],[f5])).
% 2.59/0.99  
% 2.59/0.99  fof(f49,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f2,axiom,(
% 2.59/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f46,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f2])).
% 2.59/0.99  
% 2.59/0.99  fof(f6,axiom,(
% 2.59/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f50,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f6])).
% 2.59/0.99  
% 2.59/0.99  fof(f67,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f46,f50])).
% 2.59/0.99  
% 2.59/0.99  fof(f69,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f49,f67])).
% 2.59/0.99  
% 2.59/0.99  fof(f52,plain,(
% 2.59/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f35])).
% 2.59/0.99  
% 2.59/0.99  fof(f11,axiom,(
% 2.59/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0)))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f25,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f11])).
% 2.59/0.99  
% 2.59/0.99  fof(f36,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0) & (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.99    inference(nnf_transformation,[],[f25])).
% 2.59/0.99  
% 2.59/0.99  fof(f57,plain,(
% 2.59/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f36])).
% 2.59/0.99  
% 2.59/0.99  fof(f62,plain,(
% 2.59/0.99    l1_pre_topc(sK0)),
% 2.59/0.99    inference(cnf_transformation,[],[f42])).
% 2.59/0.99  
% 2.59/0.99  fof(f12,axiom,(
% 2.59/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f26,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f12])).
% 2.59/0.99  
% 2.59/0.99  fof(f37,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.99    inference(nnf_transformation,[],[f26])).
% 2.59/0.99  
% 2.59/0.99  fof(f58,plain,(
% 2.59/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f37])).
% 2.59/0.99  
% 2.59/0.99  fof(f1,axiom,(
% 2.59/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f33,plain,(
% 2.59/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.99    inference(nnf_transformation,[],[f1])).
% 2.59/0.99  
% 2.59/0.99  fof(f34,plain,(
% 2.59/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.99    inference(flattening,[],[f33])).
% 2.59/0.99  
% 2.59/0.99  fof(f43,plain,(
% 2.59/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f71,plain,(
% 2.59/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.59/0.99    inference(equality_resolution,[],[f43])).
% 2.59/0.99  
% 2.59/0.99  fof(f45,plain,(
% 2.59/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f13,axiom,(
% 2.59/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f27,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f13])).
% 2.59/0.99  
% 2.59/0.99  fof(f28,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.99    inference(flattening,[],[f27])).
% 2.59/0.99  
% 2.59/0.99  fof(f60,plain,(
% 2.59/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f28])).
% 2.59/0.99  
% 2.59/0.99  fof(f65,plain,(
% 2.59/0.99    k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)),
% 2.59/0.99    inference(cnf_transformation,[],[f42])).
% 2.59/0.99  
% 2.59/0.99  fof(f59,plain,(
% 2.59/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f37])).
% 2.59/0.99  
% 2.59/0.99  fof(f56,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f36])).
% 2.59/0.99  
% 2.59/0.99  fof(f10,axiom,(
% 2.59/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f24,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f10])).
% 2.59/0.99  
% 2.59/0.99  fof(f55,plain,(
% 2.59/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f3,axiom,(
% 2.59/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f18,plain,(
% 2.59/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.99    inference(ennf_transformation,[],[f3])).
% 2.59/0.99  
% 2.59/0.99  fof(f47,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f18])).
% 2.59/0.99  
% 2.59/0.99  fof(f68,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f47,f67])).
% 2.59/0.99  
% 2.59/0.99  fof(f9,axiom,(
% 2.59/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f23,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/1.00    inference(ennf_transformation,[],[f9])).
% 2.59/1.00  
% 2.59/1.00  fof(f54,plain,(
% 2.59/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f23])).
% 2.59/1.00  
% 2.59/1.00  fof(f8,axiom,(
% 2.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f17,plain,(
% 2.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 2.59/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.59/1.00  
% 2.59/1.00  fof(f21,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/1.00    inference(ennf_transformation,[],[f17])).
% 2.59/1.00  
% 2.59/1.00  fof(f22,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/1.00    inference(flattening,[],[f21])).
% 2.59/1.00  
% 2.59/1.00  fof(f53,plain,(
% 2.59/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f22])).
% 2.59/1.00  
% 2.59/1.00  fof(f64,plain,(
% 2.59/1.00    v4_pre_topc(sK1,sK0)),
% 2.59/1.00    inference(cnf_transformation,[],[f42])).
% 2.59/1.00  
% 2.59/1.00  fof(f4,axiom,(
% 2.59/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f19,plain,(
% 2.59/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/1.00    inference(ennf_transformation,[],[f4])).
% 2.59/1.00  
% 2.59/1.00  fof(f48,plain,(
% 2.59/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/1.00    inference(cnf_transformation,[],[f19])).
% 2.59/1.00  
% 2.59/1.00  fof(f14,axiom,(
% 2.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 2.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.00  
% 2.59/1.00  fof(f29,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/1.00    inference(ennf_transformation,[],[f14])).
% 2.59/1.00  
% 2.59/1.00  fof(f30,plain,(
% 2.59/1.00    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/1.00    inference(flattening,[],[f29])).
% 2.59/1.00  
% 2.59/1.00  fof(f61,plain,(
% 2.59/1.00    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/1.00    inference(cnf_transformation,[],[f30])).
% 2.59/1.00  
% 2.59/1.00  fof(f66,plain,(
% 2.59/1.00    k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)),
% 2.59/1.00    inference(cnf_transformation,[],[f42])).
% 2.59/1.00  
% 2.59/1.00  cnf(c_20,negated_conjecture,
% 2.59/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.59/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1570,plain,
% 2.59/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_7,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1571,plain,
% 2.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.59/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1882,plain,
% 2.59/1.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_1570,c_1571]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_5,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.59/1.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.59/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6,plain,
% 2.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_172,plain,
% 2.59/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.59/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_173,plain,
% 2.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.59/1.00      inference(renaming,[status(thm)],[c_172]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_211,plain,
% 2.59/1.00      ( ~ r1_tarski(X0,X1)
% 2.59/1.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.59/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_173]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1567,plain,
% 2.59/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.59/1.00      | r1_tarski(X0,X2) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3300,plain,
% 2.59/1.00      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_1882,c_1567]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_11,plain,
% 2.59/1.00      ( v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.59/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_21,negated_conjecture,
% 2.59/1.00      ( l1_pre_topc(sK0) ),
% 2.59/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_402,plain,
% 2.59/1.00      ( v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_403,plain,
% 2.59/1.00      ( v2_tops_1(X0,sK0)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_402]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_14,plain,
% 2.59/1.00      ( ~ v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(X1,X0))
% 2.59/1.00      | ~ l1_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_357,plain,
% 2.59/1.00      ( ~ v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(X1,X0))
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_358,plain,
% 2.59/1.00      ( ~ v2_tops_1(X0,sK0)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_357]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_465,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0))
% 2.59/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.59/1.00      inference(resolution,[status(thm)],[c_403,c_358]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_467,plain,
% 2.59/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.59/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_465]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_850,plain,
% 2.59/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.59/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.59/1.00      inference(prop_impl,[status(thm)],[c_20,c_467]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1559,plain,
% 2.59/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.59/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2,plain,
% 2.59/1.00      ( r1_tarski(X0,X0) ),
% 2.59/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_70,plain,
% 2.59/1.00      ( r1_tarski(sK1,sK1) ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_69,plain,
% 2.59/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_71,plain,
% 2.59/1.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_69]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_0,plain,
% 2.59/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.59/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_74,plain,
% 2.59/1.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_15,plain,
% 2.59/1.00      ( ~ v3_tops_1(X0,X1)
% 2.59/1.00      | v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_18,negated_conjecture,
% 2.59/1.00      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.59/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_176,plain,
% 2.59/1.00      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.59/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_337,plain,
% 2.59/1.00      ( v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | k2_tops_1(sK0,sK1) = sK1
% 2.59/1.00      | sK1 != X0
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_176]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_338,plain,
% 2.59/1.00      ( v2_tops_1(sK1,sK0)
% 2.59/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | ~ l1_pre_topc(sK0)
% 2.59/1.00      | k2_tops_1(sK0,sK1) = sK1 ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_337]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_340,plain,
% 2.59/1.00      ( v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_338,c_21,c_20]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_505,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0))
% 2.59/1.00      | k2_tops_1(sK0,sK1) = sK1
% 2.59/1.00      | sK1 != X0
% 2.59/1.00      | sK0 != sK0 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_340,c_358]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_506,plain,
% 2.59/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.59/1.00      | k2_tops_1(sK0,sK1) = sK1 ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_505]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_508,plain,
% 2.59/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_506,c_20]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_510,plain,
% 2.59/1.00      ( k2_tops_1(sK0,sK1) = sK1
% 2.59/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1140,plain,
% 2.59/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.59/1.00      theory(equality) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1702,plain,
% 2.59/1.00      ( ~ r1_tarski(X0,X1)
% 2.59/1.00      | r1_tarski(X2,k2_tops_1(sK0,X2))
% 2.59/1.00      | X2 != X0
% 2.59/1.00      | k2_tops_1(sK0,X2) != X1 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_1140]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1703,plain,
% 2.59/1.00      ( X0 != X1
% 2.59/1.00      | k2_tops_1(sK0,X0) != X2
% 2.59/1.00      | r1_tarski(X1,X2) != iProver_top
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0)) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1702]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1705,plain,
% 2.59/1.00      ( k2_tops_1(sK0,sK1) != sK1
% 2.59/1.00      | sK1 != sK1
% 2.59/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
% 2.59/1.00      | r1_tarski(sK1,sK1) != iProver_top ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_1703]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1801,plain,
% 2.59/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_1559,c_70,c_71,c_74,c_510,c_1705]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1572,plain,
% 2.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.59/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_13,plain,
% 2.59/1.00      ( v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 2.59/1.00      | ~ l1_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_372,plain,
% 2.59/1.00      ( v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_373,plain,
% 2.59/1.00      ( v2_tops_1(X0,sK0)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_372]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_12,plain,
% 2.59/1.00      ( ~ v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.59/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_387,plain,
% 2.59/1.00      ( ~ v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_388,plain,
% 2.59/1.00      ( ~ v2_tops_1(X0,sK0)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_479,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
% 2.59/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.59/1.00      inference(resolution,[status(thm)],[c_373,c_388]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1563,plain,
% 2.59/1.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.59/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1888,plain,
% 2.59/1.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top
% 2.59/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_1572,c_1563]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2202,plain,
% 2.59/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.59/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_1801,c_1888]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_23,plain,
% 2.59/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_480,plain,
% 2.59/1.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.59/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.59/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_482,plain,
% 2.59/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.59/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.59/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_480]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2289,plain,
% 2.59/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_2202,c_23,c_70,c_71,c_74,c_482,c_510,c_1705]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_10,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.59/1.00      | ~ l1_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_417,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_418,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_417]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1566,plain,
% 2.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.59/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1698,plain,
% 2.59/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_1570,c_1566]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2293,plain,
% 2.59/1.00      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 2.59/1.00      inference(demodulation,[status(thm)],[c_2289,c_1698]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.59/1.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 2.59/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_209,plain,
% 2.59/1.00      ( ~ r1_tarski(X0,X1)
% 2.59/1.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 2.59/1.00      inference(bin_hyper_res,[status(thm)],[c_3,c_173]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1569,plain,
% 2.59/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 2.59/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3197,plain,
% 2.59/1.00      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_xboole_0))) = k3_subset_1(sK1,k1_xboole_0) ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_2293,c_1569]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3587,plain,
% 2.59/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_subset_1(sK1,k1_xboole_0) ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3300,c_3197]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_9,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.59/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_429,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_430,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_429]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1565,plain,
% 2.59/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.59/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1718,plain,
% 2.59/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_1570,c_1565]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_8,plain,
% 2.59/1.00      ( ~ v4_pre_topc(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 2.59/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_19,negated_conjecture,
% 2.59/1.00      ( v4_pre_topc(sK1,sK0) ),
% 2.59/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_313,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | k2_pre_topc(X1,X0) = X0
% 2.59/1.00      | sK1 != X0
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_314,plain,
% 2.59/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | ~ l1_pre_topc(sK0)
% 2.59/1.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_313]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_316,plain,
% 2.59/1.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_314,c_21,c_20]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1719,plain,
% 2.59/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.59/1.00      inference(light_normalisation,[status(thm)],[c_1718,c_316]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2292,plain,
% 2.59/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.59/1.00      inference(demodulation,[status(thm)],[c_2289,c_1719]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3590,plain,
% 2.59/1.00      ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
% 2.59/1.00      inference(demodulation,[status(thm)],[c_3587,c_2292]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3632,plain,
% 2.59/1.00      ( r1_tarski(sK1,k3_subset_1(sK1,k1_xboole_0)) = iProver_top ),
% 2.59/1.00      inference(demodulation,[status(thm)],[c_3590,c_1801]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.59/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.59/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_210,plain,
% 2.59/1.00      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 2.59/1.00      | ~ r1_tarski(X1,X0) ),
% 2.59/1.00      inference(bin_hyper_res,[status(thm)],[c_4,c_173]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1568,plain,
% 2.59/1.00      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 2.59/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2718,plain,
% 2.59/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.59/1.00      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_1568,c_1571]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1574,plain,
% 2.59/1.00      ( X0 = X1
% 2.59/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.59/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3104,plain,
% 2.59/1.00      ( k3_subset_1(X0,X1) = X0
% 2.59/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.59/1.00      | r1_tarski(X0,k3_subset_1(X0,X1)) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_2718,c_1574]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4001,plain,
% 2.59/1.00      ( k3_subset_1(sK1,k1_xboole_0) = sK1
% 2.59/1.00      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.59/1.00      inference(superposition,[status(thm)],[c_3632,c_3104]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_16,plain,
% 2.59/1.00      ( v3_tops_1(X0,X1)
% 2.59/1.00      | ~ v2_tops_1(X0,X1)
% 2.59/1.00      | ~ v4_pre_topc(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1) ),
% 2.59/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_299,plain,
% 2.59/1.00      ( v3_tops_1(X0,X1)
% 2.59/1.00      | ~ v2_tops_1(X0,X1)
% 2.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.59/1.00      | ~ l1_pre_topc(X1)
% 2.59/1.00      | sK1 != X0
% 2.59/1.00      | sK0 != X1 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_300,plain,
% 2.59/1.00      ( v3_tops_1(sK1,sK0)
% 2.59/1.00      | ~ v2_tops_1(sK1,sK0)
% 2.59/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | ~ l1_pre_topc(sK0) ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_299]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_302,plain,
% 2.59/1.00      ( v3_tops_1(sK1,sK0) | ~ v2_tops_1(sK1,sK0) ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_300,c_21,c_20]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_17,negated_conjecture,
% 2.59/1.00      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.59/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_174,plain,
% 2.59/1.00      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.59/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_325,plain,
% 2.59/1.00      ( ~ v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.59/1.00      inference(resolution,[status(thm)],[c_302,c_174]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_530,plain,
% 2.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
% 2.59/1.00      | k2_tops_1(sK0,sK1) != sK1
% 2.59/1.00      | sK1 != X0
% 2.59/1.00      | sK0 != sK0 ),
% 2.59/1.00      inference(resolution_lifted,[status(thm)],[c_325,c_373]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_531,plain,
% 2.59/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.59/1.00      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.59/1.00      | k2_tops_1(sK0,sK1) != sK1 ),
% 2.59/1.00      inference(unflattening,[status(thm)],[c_530]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_533,plain,
% 2.59/1.00      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_531,c_20]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_846,plain,
% 2.59/1.00      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.59/1.00      inference(prop_impl,[status(thm)],[c_20,c_531]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_1561,plain,
% 2.59/1.00      ( k2_tops_1(sK0,sK1) != sK1
% 2.59/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_535,plain,
% 2.59/1.00      ( k2_tops_1(sK0,sK1) != sK1
% 2.59/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 2.59/1.00      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_2403,plain,
% 2.59/1.00      ( k2_tops_1(sK0,sK1) != sK1 ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_1561,c_70,c_71,c_74,c_510,c_535,c_1705]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3631,plain,
% 2.59/1.00      ( k3_subset_1(sK1,k1_xboole_0) != sK1 ),
% 2.59/1.00      inference(demodulation,[status(thm)],[c_3590,c_2403]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(contradiction,plain,
% 2.59/1.00      ( $false ),
% 2.59/1.00      inference(minisat,[status(thm)],[c_4001,c_3631,c_2293]) ).
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  ------                               Statistics
% 2.59/1.00  
% 2.59/1.00  ------ General
% 2.59/1.00  
% 2.59/1.00  abstr_ref_over_cycles:                  0
% 2.59/1.00  abstr_ref_under_cycles:                 0
% 2.59/1.00  gc_basic_clause_elim:                   0
% 2.59/1.00  forced_gc_time:                         0
% 2.59/1.00  parsing_time:                           0.009
% 2.59/1.00  unif_index_cands_time:                  0.
% 2.59/1.00  unif_index_add_time:                    0.
% 2.59/1.00  orderings_time:                         0.
% 2.59/1.00  out_proof_time:                         0.008
% 2.59/1.00  total_time:                             0.138
% 2.59/1.00  num_of_symbols:                         50
% 2.59/1.00  num_of_terms:                           2601
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing
% 2.59/1.00  
% 2.59/1.00  num_of_splits:                          0
% 2.59/1.00  num_of_split_atoms:                     0
% 2.59/1.00  num_of_reused_defs:                     0
% 2.59/1.00  num_eq_ax_congr_red:                    21
% 2.59/1.00  num_of_sem_filtered_clauses:            1
% 2.59/1.00  num_of_subtypes:                        0
% 2.59/1.00  monotx_restored_types:                  0
% 2.59/1.00  sat_num_of_epr_types:                   0
% 2.59/1.00  sat_num_of_non_cyclic_types:            0
% 2.59/1.00  sat_guarded_non_collapsed_types:        0
% 2.59/1.00  num_pure_diseq_elim:                    0
% 2.59/1.00  simp_replaced_by:                       0
% 2.59/1.00  res_preprocessed:                       97
% 2.59/1.00  prep_upred:                             0
% 2.59/1.00  prep_unflattend:                        46
% 2.59/1.00  smt_new_axioms:                         0
% 2.59/1.00  pred_elim_cands:                        2
% 2.59/1.00  pred_elim:                              4
% 2.59/1.00  pred_elim_cl:                           4
% 2.59/1.00  pred_elim_cycles:                       6
% 2.59/1.00  merged_defs:                            22
% 2.59/1.00  merged_defs_ncl:                        0
% 2.59/1.00  bin_hyper_res:                          25
% 2.59/1.00  prep_cycles:                            4
% 2.59/1.00  pred_elim_time:                         0.012
% 2.59/1.00  splitting_time:                         0.
% 2.59/1.00  sem_filter_time:                        0.
% 2.59/1.00  monotx_time:                            0.001
% 2.59/1.00  subtype_inf_time:                       0.
% 2.59/1.00  
% 2.59/1.00  ------ Problem properties
% 2.59/1.00  
% 2.59/1.00  clauses:                                17
% 2.59/1.00  conjectures:                            1
% 2.59/1.00  epr:                                    2
% 2.59/1.00  horn:                                   16
% 2.59/1.00  ground:                                 6
% 2.59/1.00  unary:                                  3
% 2.59/1.00  binary:                                 11
% 2.59/1.00  lits:                                   34
% 2.59/1.00  lits_eq:                                11
% 2.59/1.00  fd_pure:                                0
% 2.59/1.00  fd_pseudo:                              0
% 2.59/1.00  fd_cond:                                0
% 2.59/1.00  fd_pseudo_cond:                         1
% 2.59/1.00  ac_symbols:                             0
% 2.59/1.00  
% 2.59/1.00  ------ Propositional Solver
% 2.59/1.00  
% 2.59/1.00  prop_solver_calls:                      30
% 2.59/1.00  prop_fast_solver_calls:                 679
% 2.59/1.00  smt_solver_calls:                       0
% 2.59/1.00  smt_fast_solver_calls:                  0
% 2.59/1.00  prop_num_of_clauses:                    1128
% 2.59/1.00  prop_preprocess_simplified:             4211
% 2.59/1.00  prop_fo_subsumed:                       15
% 2.59/1.00  prop_solver_time:                       0.
% 2.59/1.00  smt_solver_time:                        0.
% 2.59/1.00  smt_fast_solver_time:                   0.
% 2.59/1.00  prop_fast_solver_time:                  0.
% 2.59/1.00  prop_unsat_core_time:                   0.
% 2.59/1.00  
% 2.59/1.00  ------ QBF
% 2.59/1.00  
% 2.59/1.00  qbf_q_res:                              0
% 2.59/1.00  qbf_num_tautologies:                    0
% 2.59/1.00  qbf_prep_cycles:                        0
% 2.59/1.00  
% 2.59/1.00  ------ BMC1
% 2.59/1.00  
% 2.59/1.00  bmc1_current_bound:                     -1
% 2.59/1.00  bmc1_last_solved_bound:                 -1
% 2.59/1.00  bmc1_unsat_core_size:                   -1
% 2.59/1.00  bmc1_unsat_core_parents_size:           -1
% 2.59/1.00  bmc1_merge_next_fun:                    0
% 2.59/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.59/1.00  
% 2.59/1.00  ------ Instantiation
% 2.59/1.00  
% 2.59/1.00  inst_num_of_clauses:                    370
% 2.59/1.00  inst_num_in_passive:                    18
% 2.59/1.00  inst_num_in_active:                     233
% 2.59/1.00  inst_num_in_unprocessed:                120
% 2.59/1.00  inst_num_of_loops:                      250
% 2.59/1.00  inst_num_of_learning_restarts:          0
% 2.59/1.00  inst_num_moves_active_passive:          12
% 2.59/1.00  inst_lit_activity:                      0
% 2.59/1.00  inst_lit_activity_moves:                0
% 2.59/1.00  inst_num_tautologies:                   0
% 2.59/1.00  inst_num_prop_implied:                  0
% 2.59/1.00  inst_num_existing_simplified:           0
% 2.59/1.00  inst_num_eq_res_simplified:             0
% 2.59/1.00  inst_num_child_elim:                    0
% 2.59/1.00  inst_num_of_dismatching_blockings:      147
% 2.59/1.00  inst_num_of_non_proper_insts:           584
% 2.59/1.00  inst_num_of_duplicates:                 0
% 2.59/1.00  inst_inst_num_from_inst_to_res:         0
% 2.59/1.00  inst_dismatching_checking_time:         0.
% 2.59/1.00  
% 2.59/1.00  ------ Resolution
% 2.59/1.00  
% 2.59/1.00  res_num_of_clauses:                     0
% 2.59/1.00  res_num_in_passive:                     0
% 2.59/1.00  res_num_in_active:                      0
% 2.59/1.00  res_num_of_loops:                       101
% 2.59/1.00  res_forward_subset_subsumed:            45
% 2.59/1.00  res_backward_subset_subsumed:           2
% 2.59/1.00  res_forward_subsumed:                   0
% 2.59/1.00  res_backward_subsumed:                  0
% 2.59/1.00  res_forward_subsumption_resolution:     0
% 2.59/1.00  res_backward_subsumption_resolution:    0
% 2.59/1.00  res_clause_to_clause_subsumption:       333
% 2.59/1.00  res_orphan_elimination:                 0
% 2.59/1.00  res_tautology_del:                      117
% 2.59/1.00  res_num_eq_res_simplified:              0
% 2.59/1.00  res_num_sel_changes:                    0
% 2.59/1.00  res_moves_from_active_to_pass:          0
% 2.59/1.00  
% 2.59/1.00  ------ Superposition
% 2.59/1.00  
% 2.59/1.00  sup_time_total:                         0.
% 2.59/1.00  sup_time_generating:                    0.
% 2.59/1.00  sup_time_sim_full:                      0.
% 2.59/1.00  sup_time_sim_immed:                     0.
% 2.59/1.00  
% 2.59/1.00  sup_num_of_clauses:                     59
% 2.59/1.00  sup_num_in_active:                      40
% 2.59/1.00  sup_num_in_passive:                     19
% 2.59/1.00  sup_num_of_loops:                       49
% 2.59/1.00  sup_fw_superposition:                   37
% 2.59/1.00  sup_bw_superposition:                   23
% 2.59/1.00  sup_immediate_simplified:               7
% 2.59/1.00  sup_given_eliminated:                   1
% 2.59/1.00  comparisons_done:                       0
% 2.59/1.00  comparisons_avoided:                    0
% 2.59/1.00  
% 2.59/1.00  ------ Simplifications
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  sim_fw_subset_subsumed:                 4
% 2.59/1.00  sim_bw_subset_subsumed:                 1
% 2.59/1.00  sim_fw_subsumed:                        1
% 2.59/1.00  sim_bw_subsumed:                        0
% 2.59/1.00  sim_fw_subsumption_res:                 1
% 2.59/1.00  sim_bw_subsumption_res:                 0
% 2.59/1.00  sim_tautology_del:                      1
% 2.59/1.00  sim_eq_tautology_del:                   1
% 2.59/1.00  sim_eq_res_simp:                        0
% 2.59/1.00  sim_fw_demodulated:                     0
% 2.59/1.00  sim_bw_demodulated:                     18
% 2.59/1.00  sim_light_normalised:                   3
% 2.59/1.00  sim_joinable_taut:                      0
% 2.59/1.00  sim_joinable_simp:                      0
% 2.59/1.00  sim_ac_normalised:                      0
% 2.59/1.00  sim_smt_subsumption:                    0
% 2.59/1.00  
%------------------------------------------------------------------------------
