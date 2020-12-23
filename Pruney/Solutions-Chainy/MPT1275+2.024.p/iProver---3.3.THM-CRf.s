%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:27 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  177 (1741 expanded)
%              Number of clauses        :  106 ( 479 expanded)
%              Number of leaves         :   18 ( 375 expanded)
%              Depth                    :   20
%              Number of atoms          :  506 (8448 expanded)
%              Number of equality atoms :  182 (2320 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

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

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_tops_1(X0,X1) != k1_xboole_0 )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_xboole_0
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f65,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_tops_1(X0,X1) != k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1957,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1958,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2245,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1958])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1959,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1949,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_2253,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_1949])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_180,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_180])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_181])).

cnf(c_1956,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_3607,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_tops_1(sK0,X0)))) = k3_subset_1(X0,k1_tops_1(sK0,X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_1956])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1960,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_224,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_181])).

cnf(c_1954,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_4196,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1960,c_1954])).

cnf(c_4883,plain,
    ( k7_subset_1(X0,X0,k1_tops_1(sK0,X0)) = k3_subset_1(X0,k1_tops_1(sK0,X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3607,c_4196])).

cnf(c_4891,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2245,c_4883])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_400,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_401,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_1951,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_2134,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1951])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_74,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_78,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_385,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_386,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_388,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_403,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_19,negated_conjecture,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_184,plain,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( v2_tops_1(X0,X1)
    | ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_355,plain,
    ( v2_tops_1(X0,X1)
    | ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_356,plain,
    ( v2_tops_1(X0,sK0)
    | ~ v3_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_504,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = sK1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_356])).

cnf(c_505,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_507,plain,
    ( v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_21])).

cnf(c_1488,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2104,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_tops_1(sK0,X2))
    | X2 != X0
    | k2_tops_1(sK0,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_2106,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | k2_tops_1(sK0,sK1) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_2137,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2134,c_21,c_74,c_78,c_388,c_403,c_507,c_2106])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_1948,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_2480,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1957,c_1948])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_317,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_319,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_22,c_21])).

cnf(c_2482,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2480,c_319,c_2137])).

cnf(c_4198,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_2245,c_1954])).

cnf(c_4377,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_4198,c_4196])).

cnf(c_4655,plain,
    ( k7_subset_1(sK1,sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2482,c_4377])).

cnf(c_4898,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4891,c_2137,c_4655])).

cnf(c_16,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_370,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_371,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_1953,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_2637,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1953])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_372,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_374,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_415,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_416,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_847,plain,
    ( v2_tops_1(X0,sK0)
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_416])).

cnf(c_848,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_849,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_2651,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2637,c_21,c_24,c_74,c_78,c_374,c_388,c_403,c_507,c_849,c_2106])).

cnf(c_4997,plain,
    ( r1_tarski(sK1,k3_subset_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4898,c_2651])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_223,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_181])).

cnf(c_1955,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_3382,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_1958])).

cnf(c_1961,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3449,plain,
    ( k3_subset_1(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,k3_subset_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3382,c_1961])).

cnf(c_5342,plain,
    ( k3_subset_1(sK1,k1_xboole_0) = sK1
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4997,c_3449])).

cnf(c_18,negated_conjecture,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_182,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
    | v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_340,plain,
    ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
    | v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_341,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | v3_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_532,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) != sK1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_341])).

cnf(c_533,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_535,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_21])).

cnf(c_1024,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_21,c_533])).

cnf(c_1945,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_1982,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1945,c_319])).

cnf(c_4999,plain,
    ( k3_subset_1(sK1,k1_xboole_0) != sK1
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4898,c_1982])).

cnf(c_2102,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1949])).

cnf(c_2140,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2137,c_2102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5342,c_4999,c_2140,c_2137,c_849])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:02:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.69/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/1.00  
% 2.69/1.00  ------  iProver source info
% 2.69/1.00  
% 2.69/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.69/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/1.00  git: non_committed_changes: false
% 2.69/1.00  git: last_make_outside_of_git: false
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options
% 2.69/1.00  
% 2.69/1.00  --out_options                           all
% 2.69/1.00  --tptp_safe_out                         true
% 2.69/1.00  --problem_path                          ""
% 2.69/1.00  --include_path                          ""
% 2.69/1.00  --clausifier                            res/vclausify_rel
% 2.69/1.00  --clausifier_options                    --mode clausify
% 2.69/1.00  --stdin                                 false
% 2.69/1.00  --stats_out                             all
% 2.69/1.00  
% 2.69/1.00  ------ General Options
% 2.69/1.00  
% 2.69/1.00  --fof                                   false
% 2.69/1.00  --time_out_real                         305.
% 2.69/1.00  --time_out_virtual                      -1.
% 2.69/1.00  --symbol_type_check                     false
% 2.69/1.00  --clausify_out                          false
% 2.69/1.00  --sig_cnt_out                           false
% 2.69/1.00  --trig_cnt_out                          false
% 2.69/1.00  --trig_cnt_out_tolerance                1.
% 2.69/1.00  --trig_cnt_out_sk_spl                   false
% 2.69/1.00  --abstr_cl_out                          false
% 2.69/1.00  
% 2.69/1.00  ------ Global Options
% 2.69/1.00  
% 2.69/1.00  --schedule                              default
% 2.69/1.00  --add_important_lit                     false
% 2.69/1.00  --prop_solver_per_cl                    1000
% 2.69/1.00  --min_unsat_core                        false
% 2.69/1.00  --soft_assumptions                      false
% 2.69/1.00  --soft_lemma_size                       3
% 2.69/1.00  --prop_impl_unit_size                   0
% 2.69/1.00  --prop_impl_unit                        []
% 2.69/1.00  --share_sel_clauses                     true
% 2.69/1.00  --reset_solvers                         false
% 2.69/1.00  --bc_imp_inh                            [conj_cone]
% 2.69/1.00  --conj_cone_tolerance                   3.
% 2.69/1.00  --extra_neg_conj                        none
% 2.69/1.00  --large_theory_mode                     true
% 2.69/1.00  --prolific_symb_bound                   200
% 2.69/1.00  --lt_threshold                          2000
% 2.69/1.00  --clause_weak_htbl                      true
% 2.69/1.00  --gc_record_bc_elim                     false
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing Options
% 2.69/1.00  
% 2.69/1.00  --preprocessing_flag                    true
% 2.69/1.00  --time_out_prep_mult                    0.1
% 2.69/1.00  --splitting_mode                        input
% 2.69/1.00  --splitting_grd                         true
% 2.69/1.00  --splitting_cvd                         false
% 2.69/1.00  --splitting_cvd_svl                     false
% 2.69/1.00  --splitting_nvd                         32
% 2.69/1.00  --sub_typing                            true
% 2.69/1.00  --prep_gs_sim                           true
% 2.69/1.00  --prep_unflatten                        true
% 2.69/1.00  --prep_res_sim                          true
% 2.69/1.00  --prep_upred                            true
% 2.69/1.00  --prep_sem_filter                       exhaustive
% 2.69/1.00  --prep_sem_filter_out                   false
% 2.69/1.00  --pred_elim                             true
% 2.69/1.00  --res_sim_input                         true
% 2.69/1.00  --eq_ax_congr_red                       true
% 2.69/1.00  --pure_diseq_elim                       true
% 2.69/1.00  --brand_transform                       false
% 2.69/1.00  --non_eq_to_eq                          false
% 2.69/1.00  --prep_def_merge                        true
% 2.69/1.00  --prep_def_merge_prop_impl              false
% 2.69/1.00  --prep_def_merge_mbd                    true
% 2.69/1.00  --prep_def_merge_tr_red                 false
% 2.69/1.00  --prep_def_merge_tr_cl                  false
% 2.69/1.00  --smt_preprocessing                     true
% 2.69/1.00  --smt_ac_axioms                         fast
% 2.69/1.00  --preprocessed_out                      false
% 2.69/1.00  --preprocessed_stats                    false
% 2.69/1.00  
% 2.69/1.00  ------ Abstraction refinement Options
% 2.69/1.00  
% 2.69/1.00  --abstr_ref                             []
% 2.69/1.00  --abstr_ref_prep                        false
% 2.69/1.00  --abstr_ref_until_sat                   false
% 2.69/1.00  --abstr_ref_sig_restrict                funpre
% 2.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.00  --abstr_ref_under                       []
% 2.69/1.00  
% 2.69/1.00  ------ SAT Options
% 2.69/1.00  
% 2.69/1.00  --sat_mode                              false
% 2.69/1.00  --sat_fm_restart_options                ""
% 2.69/1.00  --sat_gr_def                            false
% 2.69/1.00  --sat_epr_types                         true
% 2.69/1.00  --sat_non_cyclic_types                  false
% 2.69/1.00  --sat_finite_models                     false
% 2.69/1.00  --sat_fm_lemmas                         false
% 2.69/1.00  --sat_fm_prep                           false
% 2.69/1.00  --sat_fm_uc_incr                        true
% 2.69/1.00  --sat_out_model                         small
% 2.69/1.00  --sat_out_clauses                       false
% 2.69/1.00  
% 2.69/1.00  ------ QBF Options
% 2.69/1.00  
% 2.69/1.00  --qbf_mode                              false
% 2.69/1.00  --qbf_elim_univ                         false
% 2.69/1.00  --qbf_dom_inst                          none
% 2.69/1.00  --qbf_dom_pre_inst                      false
% 2.69/1.00  --qbf_sk_in                             false
% 2.69/1.00  --qbf_pred_elim                         true
% 2.69/1.00  --qbf_split                             512
% 2.69/1.00  
% 2.69/1.00  ------ BMC1 Options
% 2.69/1.00  
% 2.69/1.00  --bmc1_incremental                      false
% 2.69/1.00  --bmc1_axioms                           reachable_all
% 2.69/1.00  --bmc1_min_bound                        0
% 2.69/1.00  --bmc1_max_bound                        -1
% 2.69/1.00  --bmc1_max_bound_default                -1
% 2.69/1.00  --bmc1_symbol_reachability              true
% 2.69/1.00  --bmc1_property_lemmas                  false
% 2.69/1.00  --bmc1_k_induction                      false
% 2.69/1.00  --bmc1_non_equiv_states                 false
% 2.69/1.00  --bmc1_deadlock                         false
% 2.69/1.00  --bmc1_ucm                              false
% 2.69/1.00  --bmc1_add_unsat_core                   none
% 2.69/1.00  --bmc1_unsat_core_children              false
% 2.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.00  --bmc1_out_stat                         full
% 2.69/1.00  --bmc1_ground_init                      false
% 2.69/1.00  --bmc1_pre_inst_next_state              false
% 2.69/1.00  --bmc1_pre_inst_state                   false
% 2.69/1.00  --bmc1_pre_inst_reach_state             false
% 2.69/1.00  --bmc1_out_unsat_core                   false
% 2.69/1.00  --bmc1_aig_witness_out                  false
% 2.69/1.00  --bmc1_verbose                          false
% 2.69/1.00  --bmc1_dump_clauses_tptp                false
% 2.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.00  --bmc1_dump_file                        -
% 2.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.00  --bmc1_ucm_extend_mode                  1
% 2.69/1.00  --bmc1_ucm_init_mode                    2
% 2.69/1.00  --bmc1_ucm_cone_mode                    none
% 2.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.00  --bmc1_ucm_relax_model                  4
% 2.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.00  --bmc1_ucm_layered_model                none
% 2.69/1.00  --bmc1_ucm_max_lemma_size               10
% 2.69/1.00  
% 2.69/1.00  ------ AIG Options
% 2.69/1.00  
% 2.69/1.00  --aig_mode                              false
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation Options
% 2.69/1.00  
% 2.69/1.00  --instantiation_flag                    true
% 2.69/1.00  --inst_sos_flag                         false
% 2.69/1.00  --inst_sos_phase                        true
% 2.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel_side                     num_symb
% 2.69/1.00  --inst_solver_per_active                1400
% 2.69/1.00  --inst_solver_calls_frac                1.
% 2.69/1.00  --inst_passive_queue_type               priority_queues
% 2.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.00  --inst_passive_queues_freq              [25;2]
% 2.69/1.00  --inst_dismatching                      true
% 2.69/1.00  --inst_eager_unprocessed_to_passive     true
% 2.69/1.00  --inst_prop_sim_given                   true
% 2.69/1.00  --inst_prop_sim_new                     false
% 2.69/1.00  --inst_subs_new                         false
% 2.69/1.00  --inst_eq_res_simp                      false
% 2.69/1.00  --inst_subs_given                       false
% 2.69/1.00  --inst_orphan_elimination               true
% 2.69/1.00  --inst_learning_loop_flag               true
% 2.69/1.00  --inst_learning_start                   3000
% 2.69/1.00  --inst_learning_factor                  2
% 2.69/1.00  --inst_start_prop_sim_after_learn       3
% 2.69/1.00  --inst_sel_renew                        solver
% 2.69/1.00  --inst_lit_activity_flag                true
% 2.69/1.00  --inst_restr_to_given                   false
% 2.69/1.00  --inst_activity_threshold               500
% 2.69/1.00  --inst_out_proof                        true
% 2.69/1.00  
% 2.69/1.00  ------ Resolution Options
% 2.69/1.00  
% 2.69/1.00  --resolution_flag                       true
% 2.69/1.00  --res_lit_sel                           adaptive
% 2.69/1.00  --res_lit_sel_side                      none
% 2.69/1.00  --res_ordering                          kbo
% 2.69/1.00  --res_to_prop_solver                    active
% 2.69/1.00  --res_prop_simpl_new                    false
% 2.69/1.00  --res_prop_simpl_given                  true
% 2.69/1.00  --res_passive_queue_type                priority_queues
% 2.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.00  --res_passive_queues_freq               [15;5]
% 2.69/1.00  --res_forward_subs                      full
% 2.69/1.00  --res_backward_subs                     full
% 2.69/1.00  --res_forward_subs_resolution           true
% 2.69/1.00  --res_backward_subs_resolution          true
% 2.69/1.00  --res_orphan_elimination                true
% 2.69/1.00  --res_time_limit                        2.
% 2.69/1.00  --res_out_proof                         true
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Options
% 2.69/1.00  
% 2.69/1.00  --superposition_flag                    true
% 2.69/1.00  --sup_passive_queue_type                priority_queues
% 2.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.00  --demod_completeness_check              fast
% 2.69/1.00  --demod_use_ground                      true
% 2.69/1.00  --sup_to_prop_solver                    passive
% 2.69/1.00  --sup_prop_simpl_new                    true
% 2.69/1.00  --sup_prop_simpl_given                  true
% 2.69/1.00  --sup_fun_splitting                     false
% 2.69/1.00  --sup_smt_interval                      50000
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Simplification Setup
% 2.69/1.00  
% 2.69/1.00  --sup_indices_passive                   []
% 2.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_full_bw                           [BwDemod]
% 2.69/1.00  --sup_immed_triv                        [TrivRules]
% 2.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_immed_bw_main                     []
% 2.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  
% 2.69/1.00  ------ Combination Options
% 2.69/1.00  
% 2.69/1.00  --comb_res_mult                         3
% 2.69/1.00  --comb_sup_mult                         2
% 2.69/1.00  --comb_inst_mult                        10
% 2.69/1.00  
% 2.69/1.00  ------ Debug Options
% 2.69/1.00  
% 2.69/1.00  --dbg_backtrace                         false
% 2.69/1.00  --dbg_dump_prop_clauses                 false
% 2.69/1.00  --dbg_dump_prop_clauses_file            -
% 2.69/1.00  --dbg_out_stat                          false
% 2.69/1.00  ------ Parsing...
% 2.69/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/1.00  ------ Proving...
% 2.69/1.00  ------ Problem Properties 
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  clauses                                 19
% 2.69/1.00  conjectures                             1
% 2.69/1.00  EPR                                     2
% 2.69/1.00  Horn                                    18
% 2.69/1.00  unary                                   3
% 2.69/1.00  binary                                  10
% 2.69/1.00  lits                                    41
% 2.69/1.00  lits eq                                 9
% 2.69/1.00  fd_pure                                 0
% 2.69/1.00  fd_pseudo                               0
% 2.69/1.00  fd_cond                                 0
% 2.69/1.00  fd_pseudo_cond                          1
% 2.69/1.00  AC symbols                              0
% 2.69/1.00  
% 2.69/1.00  ------ Schedule dynamic 5 is on 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  Current options:
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options
% 2.69/1.00  
% 2.69/1.00  --out_options                           all
% 2.69/1.00  --tptp_safe_out                         true
% 2.69/1.00  --problem_path                          ""
% 2.69/1.00  --include_path                          ""
% 2.69/1.00  --clausifier                            res/vclausify_rel
% 2.69/1.00  --clausifier_options                    --mode clausify
% 2.69/1.00  --stdin                                 false
% 2.69/1.00  --stats_out                             all
% 2.69/1.00  
% 2.69/1.00  ------ General Options
% 2.69/1.00  
% 2.69/1.00  --fof                                   false
% 2.69/1.00  --time_out_real                         305.
% 2.69/1.00  --time_out_virtual                      -1.
% 2.69/1.00  --symbol_type_check                     false
% 2.69/1.00  --clausify_out                          false
% 2.69/1.00  --sig_cnt_out                           false
% 2.69/1.00  --trig_cnt_out                          false
% 2.69/1.00  --trig_cnt_out_tolerance                1.
% 2.69/1.00  --trig_cnt_out_sk_spl                   false
% 2.69/1.00  --abstr_cl_out                          false
% 2.69/1.00  
% 2.69/1.00  ------ Global Options
% 2.69/1.00  
% 2.69/1.00  --schedule                              default
% 2.69/1.00  --add_important_lit                     false
% 2.69/1.00  --prop_solver_per_cl                    1000
% 2.69/1.00  --min_unsat_core                        false
% 2.69/1.00  --soft_assumptions                      false
% 2.69/1.00  --soft_lemma_size                       3
% 2.69/1.00  --prop_impl_unit_size                   0
% 2.69/1.00  --prop_impl_unit                        []
% 2.69/1.00  --share_sel_clauses                     true
% 2.69/1.00  --reset_solvers                         false
% 2.69/1.00  --bc_imp_inh                            [conj_cone]
% 2.69/1.00  --conj_cone_tolerance                   3.
% 2.69/1.00  --extra_neg_conj                        none
% 2.69/1.00  --large_theory_mode                     true
% 2.69/1.00  --prolific_symb_bound                   200
% 2.69/1.00  --lt_threshold                          2000
% 2.69/1.00  --clause_weak_htbl                      true
% 2.69/1.00  --gc_record_bc_elim                     false
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing Options
% 2.69/1.00  
% 2.69/1.00  --preprocessing_flag                    true
% 2.69/1.00  --time_out_prep_mult                    0.1
% 2.69/1.00  --splitting_mode                        input
% 2.69/1.00  --splitting_grd                         true
% 2.69/1.00  --splitting_cvd                         false
% 2.69/1.00  --splitting_cvd_svl                     false
% 2.69/1.00  --splitting_nvd                         32
% 2.69/1.00  --sub_typing                            true
% 2.69/1.00  --prep_gs_sim                           true
% 2.69/1.00  --prep_unflatten                        true
% 2.69/1.00  --prep_res_sim                          true
% 2.69/1.00  --prep_upred                            true
% 2.69/1.00  --prep_sem_filter                       exhaustive
% 2.69/1.00  --prep_sem_filter_out                   false
% 2.69/1.00  --pred_elim                             true
% 2.69/1.00  --res_sim_input                         true
% 2.69/1.00  --eq_ax_congr_red                       true
% 2.69/1.00  --pure_diseq_elim                       true
% 2.69/1.00  --brand_transform                       false
% 2.69/1.00  --non_eq_to_eq                          false
% 2.69/1.00  --prep_def_merge                        true
% 2.69/1.00  --prep_def_merge_prop_impl              false
% 2.69/1.00  --prep_def_merge_mbd                    true
% 2.69/1.00  --prep_def_merge_tr_red                 false
% 2.69/1.00  --prep_def_merge_tr_cl                  false
% 2.69/1.00  --smt_preprocessing                     true
% 2.69/1.00  --smt_ac_axioms                         fast
% 2.69/1.00  --preprocessed_out                      false
% 2.69/1.00  --preprocessed_stats                    false
% 2.69/1.00  
% 2.69/1.00  ------ Abstraction refinement Options
% 2.69/1.00  
% 2.69/1.00  --abstr_ref                             []
% 2.69/1.00  --abstr_ref_prep                        false
% 2.69/1.00  --abstr_ref_until_sat                   false
% 2.69/1.00  --abstr_ref_sig_restrict                funpre
% 2.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.00  --abstr_ref_under                       []
% 2.69/1.00  
% 2.69/1.00  ------ SAT Options
% 2.69/1.00  
% 2.69/1.00  --sat_mode                              false
% 2.69/1.00  --sat_fm_restart_options                ""
% 2.69/1.00  --sat_gr_def                            false
% 2.69/1.00  --sat_epr_types                         true
% 2.69/1.00  --sat_non_cyclic_types                  false
% 2.69/1.00  --sat_finite_models                     false
% 2.69/1.00  --sat_fm_lemmas                         false
% 2.69/1.00  --sat_fm_prep                           false
% 2.69/1.00  --sat_fm_uc_incr                        true
% 2.69/1.00  --sat_out_model                         small
% 2.69/1.00  --sat_out_clauses                       false
% 2.69/1.00  
% 2.69/1.00  ------ QBF Options
% 2.69/1.00  
% 2.69/1.00  --qbf_mode                              false
% 2.69/1.00  --qbf_elim_univ                         false
% 2.69/1.00  --qbf_dom_inst                          none
% 2.69/1.00  --qbf_dom_pre_inst                      false
% 2.69/1.00  --qbf_sk_in                             false
% 2.69/1.00  --qbf_pred_elim                         true
% 2.69/1.00  --qbf_split                             512
% 2.69/1.00  
% 2.69/1.00  ------ BMC1 Options
% 2.69/1.00  
% 2.69/1.00  --bmc1_incremental                      false
% 2.69/1.00  --bmc1_axioms                           reachable_all
% 2.69/1.00  --bmc1_min_bound                        0
% 2.69/1.00  --bmc1_max_bound                        -1
% 2.69/1.00  --bmc1_max_bound_default                -1
% 2.69/1.00  --bmc1_symbol_reachability              true
% 2.69/1.00  --bmc1_property_lemmas                  false
% 2.69/1.00  --bmc1_k_induction                      false
% 2.69/1.00  --bmc1_non_equiv_states                 false
% 2.69/1.00  --bmc1_deadlock                         false
% 2.69/1.00  --bmc1_ucm                              false
% 2.69/1.00  --bmc1_add_unsat_core                   none
% 2.69/1.00  --bmc1_unsat_core_children              false
% 2.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.00  --bmc1_out_stat                         full
% 2.69/1.00  --bmc1_ground_init                      false
% 2.69/1.00  --bmc1_pre_inst_next_state              false
% 2.69/1.00  --bmc1_pre_inst_state                   false
% 2.69/1.00  --bmc1_pre_inst_reach_state             false
% 2.69/1.00  --bmc1_out_unsat_core                   false
% 2.69/1.00  --bmc1_aig_witness_out                  false
% 2.69/1.00  --bmc1_verbose                          false
% 2.69/1.00  --bmc1_dump_clauses_tptp                false
% 2.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.00  --bmc1_dump_file                        -
% 2.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.00  --bmc1_ucm_extend_mode                  1
% 2.69/1.00  --bmc1_ucm_init_mode                    2
% 2.69/1.00  --bmc1_ucm_cone_mode                    none
% 2.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.00  --bmc1_ucm_relax_model                  4
% 2.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.00  --bmc1_ucm_layered_model                none
% 2.69/1.00  --bmc1_ucm_max_lemma_size               10
% 2.69/1.00  
% 2.69/1.00  ------ AIG Options
% 2.69/1.00  
% 2.69/1.00  --aig_mode                              false
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation Options
% 2.69/1.00  
% 2.69/1.00  --instantiation_flag                    true
% 2.69/1.00  --inst_sos_flag                         false
% 2.69/1.00  --inst_sos_phase                        true
% 2.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel_side                     none
% 2.69/1.00  --inst_solver_per_active                1400
% 2.69/1.00  --inst_solver_calls_frac                1.
% 2.69/1.00  --inst_passive_queue_type               priority_queues
% 2.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.00  --inst_passive_queues_freq              [25;2]
% 2.69/1.00  --inst_dismatching                      true
% 2.69/1.00  --inst_eager_unprocessed_to_passive     true
% 2.69/1.00  --inst_prop_sim_given                   true
% 2.69/1.00  --inst_prop_sim_new                     false
% 2.69/1.00  --inst_subs_new                         false
% 2.69/1.00  --inst_eq_res_simp                      false
% 2.69/1.00  --inst_subs_given                       false
% 2.69/1.00  --inst_orphan_elimination               true
% 2.69/1.00  --inst_learning_loop_flag               true
% 2.69/1.00  --inst_learning_start                   3000
% 2.69/1.00  --inst_learning_factor                  2
% 2.69/1.00  --inst_start_prop_sim_after_learn       3
% 2.69/1.00  --inst_sel_renew                        solver
% 2.69/1.00  --inst_lit_activity_flag                true
% 2.69/1.00  --inst_restr_to_given                   false
% 2.69/1.00  --inst_activity_threshold               500
% 2.69/1.00  --inst_out_proof                        true
% 2.69/1.00  
% 2.69/1.00  ------ Resolution Options
% 2.69/1.00  
% 2.69/1.00  --resolution_flag                       false
% 2.69/1.00  --res_lit_sel                           adaptive
% 2.69/1.00  --res_lit_sel_side                      none
% 2.69/1.00  --res_ordering                          kbo
% 2.69/1.00  --res_to_prop_solver                    active
% 2.69/1.00  --res_prop_simpl_new                    false
% 2.69/1.00  --res_prop_simpl_given                  true
% 2.69/1.00  --res_passive_queue_type                priority_queues
% 2.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.00  --res_passive_queues_freq               [15;5]
% 2.69/1.00  --res_forward_subs                      full
% 2.69/1.00  --res_backward_subs                     full
% 2.69/1.00  --res_forward_subs_resolution           true
% 2.69/1.00  --res_backward_subs_resolution          true
% 2.69/1.00  --res_orphan_elimination                true
% 2.69/1.00  --res_time_limit                        2.
% 2.69/1.00  --res_out_proof                         true
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Options
% 2.69/1.00  
% 2.69/1.00  --superposition_flag                    true
% 2.69/1.00  --sup_passive_queue_type                priority_queues
% 2.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.00  --demod_completeness_check              fast
% 2.69/1.00  --demod_use_ground                      true
% 2.69/1.00  --sup_to_prop_solver                    passive
% 2.69/1.00  --sup_prop_simpl_new                    true
% 2.69/1.00  --sup_prop_simpl_given                  true
% 2.69/1.00  --sup_fun_splitting                     false
% 2.69/1.00  --sup_smt_interval                      50000
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Simplification Setup
% 2.69/1.00  
% 2.69/1.00  --sup_indices_passive                   []
% 2.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_full_bw                           [BwDemod]
% 2.69/1.00  --sup_immed_triv                        [TrivRules]
% 2.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_immed_bw_main                     []
% 2.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  
% 2.69/1.00  ------ Combination Options
% 2.69/1.00  
% 2.69/1.00  --comb_res_mult                         3
% 2.69/1.00  --comb_sup_mult                         2
% 2.69/1.00  --comb_inst_mult                        10
% 2.69/1.00  
% 2.69/1.00  ------ Debug Options
% 2.69/1.00  
% 2.69/1.00  --dbg_backtrace                         false
% 2.69/1.00  --dbg_dump_prop_clauses                 false
% 2.69/1.00  --dbg_dump_prop_clauses_file            -
% 2.69/1.00  --dbg_out_stat                          false
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ Proving...
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS status Theorem for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  fof(f15,conjecture,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f16,negated_conjecture,(
% 2.69/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.69/1.00    inference(negated_conjecture,[],[f15])).
% 2.69/1.00  
% 2.69/1.00  fof(f30,plain,(
% 2.69/1.00    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f16])).
% 2.69/1.00  
% 2.69/1.00  fof(f31,plain,(
% 2.69/1.00    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.69/1.00    inference(flattening,[],[f30])).
% 2.69/1.00  
% 2.69/1.00  fof(f38,plain,(
% 2.69/1.00    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.69/1.00    inference(nnf_transformation,[],[f31])).
% 2.69/1.00  
% 2.69/1.00  fof(f39,plain,(
% 2.69/1.00    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.69/1.00    inference(flattening,[],[f38])).
% 2.69/1.00  
% 2.69/1.00  fof(f41,plain,(
% 2.69/1.00    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK1) != sK1 | ~v3_tops_1(sK1,X0)) & (k2_tops_1(X0,sK1) = sK1 | v3_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f40,plain,(
% 2.69/1.00    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f42,plain,(
% 2.69/1.00    ((k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)) & (k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 2.69/1.00  
% 2.69/1.00  fof(f64,plain,(
% 2.69/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.69/1.00    inference(cnf_transformation,[],[f42])).
% 2.69/1.00  
% 2.69/1.00  fof(f7,axiom,(
% 2.69/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f34,plain,(
% 2.69/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.69/1.00    inference(nnf_transformation,[],[f7])).
% 2.69/1.00  
% 2.69/1.00  fof(f51,plain,(
% 2.69/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f34])).
% 2.69/1.00  
% 2.69/1.00  fof(f52,plain,(
% 2.69/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f34])).
% 2.69/1.00  
% 2.69/1.00  fof(f11,axiom,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f25,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f11])).
% 2.69/1.00  
% 2.69/1.00  fof(f57,plain,(
% 2.69/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f25])).
% 2.69/1.00  
% 2.69/1.00  fof(f63,plain,(
% 2.69/1.00    l1_pre_topc(sK0)),
% 2.69/1.00    inference(cnf_transformation,[],[f42])).
% 2.69/1.00  
% 2.69/1.00  fof(f3,axiom,(
% 2.69/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f18,plain,(
% 2.69/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/1.00    inference(ennf_transformation,[],[f3])).
% 2.69/1.00  
% 2.69/1.00  fof(f47,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f18])).
% 2.69/1.00  
% 2.69/1.00  fof(f2,axiom,(
% 2.69/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f46,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f2])).
% 2.69/1.00  
% 2.69/1.00  fof(f6,axiom,(
% 2.69/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f50,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f6])).
% 2.69/1.00  
% 2.69/1.00  fof(f68,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.69/1.00    inference(definition_unfolding,[],[f46,f50])).
% 2.69/1.00  
% 2.69/1.00  fof(f69,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/1.00    inference(definition_unfolding,[],[f47,f68])).
% 2.69/1.00  
% 2.69/1.00  fof(f1,axiom,(
% 2.69/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f32,plain,(
% 2.69/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/1.00    inference(nnf_transformation,[],[f1])).
% 2.69/1.00  
% 2.69/1.00  fof(f33,plain,(
% 2.69/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/1.00    inference(flattening,[],[f32])).
% 2.69/1.00  
% 2.69/1.00  fof(f44,plain,(
% 2.69/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.69/1.00    inference(cnf_transformation,[],[f33])).
% 2.69/1.00  
% 2.69/1.00  fof(f71,plain,(
% 2.69/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.69/1.00    inference(equality_resolution,[],[f44])).
% 2.69/1.00  
% 2.69/1.00  fof(f5,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f20,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/1.00    inference(ennf_transformation,[],[f5])).
% 2.69/1.00  
% 2.69/1.00  fof(f49,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f70,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/1.00    inference(definition_unfolding,[],[f49,f68])).
% 2.69/1.00  
% 2.69/1.00  fof(f12,axiom,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0)))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f26,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f12])).
% 2.69/1.00  
% 2.69/1.00  fof(f36,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0) & (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(nnf_transformation,[],[f26])).
% 2.69/1.00  
% 2.69/1.00  fof(f58,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f36])).
% 2.69/1.00  
% 2.69/1.00  fof(f43,plain,(
% 2.69/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.69/1.00    inference(cnf_transformation,[],[f33])).
% 2.69/1.00  
% 2.69/1.00  fof(f72,plain,(
% 2.69/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.69/1.00    inference(equality_resolution,[],[f43])).
% 2.69/1.00  
% 2.69/1.00  fof(f45,plain,(
% 2.69/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f33])).
% 2.69/1.00  
% 2.69/1.00  fof(f13,axiom,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f27,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f13])).
% 2.69/1.00  
% 2.69/1.00  fof(f37,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(nnf_transformation,[],[f27])).
% 2.69/1.00  
% 2.69/1.00  fof(f61,plain,(
% 2.69/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f66,plain,(
% 2.69/1.00    k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)),
% 2.69/1.00    inference(cnf_transformation,[],[f42])).
% 2.69/1.00  
% 2.69/1.00  fof(f14,axiom,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f28,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f14])).
% 2.69/1.00  
% 2.69/1.00  fof(f29,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(flattening,[],[f28])).
% 2.69/1.00  
% 2.69/1.00  fof(f62,plain,(
% 2.69/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f29])).
% 2.69/1.00  
% 2.69/1.00  fof(f10,axiom,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f24,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f10])).
% 2.69/1.00  
% 2.69/1.00  fof(f56,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f24])).
% 2.69/1.00  
% 2.69/1.00  fof(f8,axiom,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f17,plain,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 2.69/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.69/1.00  
% 2.69/1.00  fof(f21,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f17])).
% 2.69/1.00  
% 2.69/1.00  fof(f22,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(flattening,[],[f21])).
% 2.69/1.00  
% 2.69/1.00  fof(f53,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f65,plain,(
% 2.69/1.00    v4_pre_topc(sK1,sK0)),
% 2.69/1.00    inference(cnf_transformation,[],[f42])).
% 2.69/1.00  
% 2.69/1.00  fof(f60,plain,(
% 2.69/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f59,plain,(
% 2.69/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f36])).
% 2.69/1.00  
% 2.69/1.00  fof(f4,axiom,(
% 2.69/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f19,plain,(
% 2.69/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/1.00    inference(ennf_transformation,[],[f4])).
% 2.69/1.00  
% 2.69/1.00  fof(f48,plain,(
% 2.69/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f19])).
% 2.69/1.00  
% 2.69/1.00  fof(f67,plain,(
% 2.69/1.00    k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)),
% 2.69/1.00    inference(cnf_transformation,[],[f42])).
% 2.69/1.00  
% 2.69/1.00  fof(f9,axiom,(
% 2.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f23,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(ennf_transformation,[],[f9])).
% 2.69/1.00  
% 2.69/1.00  fof(f35,plain,(
% 2.69/1.00    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/1.00    inference(nnf_transformation,[],[f23])).
% 2.69/1.00  
% 2.69/1.00  fof(f55,plain,(
% 2.69/1.00    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f35])).
% 2.69/1.00  
% 2.69/1.00  cnf(c_21,negated_conjecture,
% 2.69/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.69/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1957,plain,
% 2.69/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_7,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1958,plain,
% 2.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.69/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2245,plain,
% 2.69/1.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1957,c_1958]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_6,plain,
% 2.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1959,plain,
% 2.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.69/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_12,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.69/1.00      | ~ l1_pre_topc(X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_22,negated_conjecture,
% 2.69/1.00      ( l1_pre_topc(sK0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_430,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.69/1.00      | sK0 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_431,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_430]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1949,plain,
% 2.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.69/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2253,plain,
% 2.69/1.00      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.69/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1959,c_1949]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/1.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_180,plain,
% 2.69/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.69/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_181,plain,
% 2.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.69/1.00      inference(renaming,[status(thm)],[c_180]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_222,plain,
% 2.69/1.00      ( ~ r1_tarski(X0,X1)
% 2.69/1.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 2.69/1.00      inference(bin_hyper_res,[status(thm)],[c_3,c_181]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1956,plain,
% 2.69/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 2.69/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3607,plain,
% 2.69/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_tops_1(sK0,X0)))) = k3_subset_1(X0,k1_tops_1(sK0,X0))
% 2.69/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2253,c_1956]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1,plain,
% 2.69/1.00      ( r1_tarski(X0,X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1960,plain,
% 2.69/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_5,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/1.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.69/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_224,plain,
% 2.69/1.00      ( ~ r1_tarski(X0,X1)
% 2.69/1.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.69/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_181]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1954,plain,
% 2.69/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.69/1.00      | r1_tarski(X0,X2) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4196,plain,
% 2.69/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1960,c_1954]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4883,plain,
% 2.69/1.00      ( k7_subset_1(X0,X0,k1_tops_1(sK0,X0)) = k3_subset_1(X0,k1_tops_1(sK0,X0))
% 2.69/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_3607,c_4196]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4891,plain,
% 2.69/1.00      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2245,c_4883]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_14,plain,
% 2.69/1.00      ( ~ v2_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | ~ l1_pre_topc(X1)
% 2.69/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_400,plain,
% 2.69/1.00      ( ~ v2_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.69/1.00      | sK0 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_401,plain,
% 2.69/1.00      ( ~ v2_tops_1(X0,sK0)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_400]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1951,plain,
% 2.69/1.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.69/1.00      | v2_tops_1(X0,sK0) != iProver_top
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2134,plain,
% 2.69/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.69/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1957,c_1951]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2,plain,
% 2.69/1.00      ( r1_tarski(X0,X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_74,plain,
% 2.69/1.00      ( r1_tarski(sK1,sK1) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_0,plain,
% 2.69/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.69/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_78,plain,
% 2.69/1.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_15,plain,
% 2.69/1.00      ( v2_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 2.69/1.00      | ~ l1_pre_topc(X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_385,plain,
% 2.69/1.00      ( v2_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 2.69/1.00      | sK0 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_386,plain,
% 2.69/1.00      ( v2_tops_1(X0,sK0)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_385]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_388,plain,
% 2.69/1.00      ( v2_tops_1(sK1,sK0)
% 2.69/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_386]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_403,plain,
% 2.69/1.00      ( ~ v2_tops_1(sK1,sK0)
% 2.69/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_401]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_19,negated_conjecture,
% 2.69/1.00      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.69/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_184,plain,
% 2.69/1.00      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.69/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_17,plain,
% 2.69/1.00      ( v2_tops_1(X0,X1)
% 2.69/1.00      | ~ v3_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | ~ l1_pre_topc(X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_355,plain,
% 2.69/1.00      ( v2_tops_1(X0,X1)
% 2.69/1.00      | ~ v3_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | sK0 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_356,plain,
% 2.69/1.00      ( v2_tops_1(X0,sK0)
% 2.69/1.00      | ~ v3_tops_1(X0,sK0)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_355]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_504,plain,
% 2.69/1.00      ( v2_tops_1(X0,sK0)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | k2_tops_1(sK0,sK1) = sK1
% 2.69/1.00      | sK1 != X0
% 2.69/1.00      | sK0 != sK0 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_184,c_356]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_505,plain,
% 2.69/1.00      ( v2_tops_1(sK1,sK0)
% 2.69/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | k2_tops_1(sK0,sK1) = sK1 ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_504]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_507,plain,
% 2.69/1.00      ( v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_505,c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1488,plain,
% 2.69/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.69/1.00      theory(equality) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2104,plain,
% 2.69/1.00      ( ~ r1_tarski(X0,X1)
% 2.69/1.00      | r1_tarski(X2,k2_tops_1(sK0,X2))
% 2.69/1.00      | X2 != X0
% 2.69/1.00      | k2_tops_1(sK0,X2) != X1 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1488]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2106,plain,
% 2.69/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.69/1.00      | ~ r1_tarski(sK1,sK1)
% 2.69/1.00      | k2_tops_1(sK0,sK1) != sK1
% 2.69/1.00      | sK1 != sK1 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_2104]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2137,plain,
% 2.69/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_2134,c_21,c_74,c_78,c_388,c_403,c_507,c_2106]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_11,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | ~ l1_pre_topc(X1)
% 2.69/1.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_442,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.69/1.00      | sK0 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_443,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_442]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1948,plain,
% 2.69/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2480,plain,
% 2.69/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1957,c_1948]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_8,plain,
% 2.69/1.00      ( ~ v4_pre_topc(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | ~ l1_pre_topc(X1)
% 2.69/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_20,negated_conjecture,
% 2.69/1.00      ( v4_pre_topc(sK1,sK0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_316,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | ~ l1_pre_topc(X1)
% 2.69/1.00      | k2_pre_topc(X1,X0) = X0
% 2.69/1.00      | sK1 != X0
% 2.69/1.00      | sK0 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_317,plain,
% 2.69/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | ~ l1_pre_topc(sK0)
% 2.69/1.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_316]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_319,plain,
% 2.69/1.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_317,c_22,c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2482,plain,
% 2.69/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_2480,c_319,c_2137]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4198,plain,
% 2.69/1.00      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2245,c_1954]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4377,plain,
% 2.69/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_4198,c_4196]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4655,plain,
% 2.69/1.00      ( k7_subset_1(sK1,sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2482,c_4377]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4898,plain,
% 2.69/1.00      ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_4891,c_2137,c_4655]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_16,plain,
% 2.69/1.00      ( ~ v2_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | r1_tarski(X0,k2_tops_1(X1,X0))
% 2.69/1.00      | ~ l1_pre_topc(X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_370,plain,
% 2.69/1.00      ( ~ v2_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | r1_tarski(X0,k2_tops_1(X1,X0))
% 2.69/1.00      | sK0 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_371,plain,
% 2.69/1.00      ( ~ v2_tops_1(X0,sK0)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_370]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1953,plain,
% 2.69/1.00      ( v2_tops_1(X0,sK0) != iProver_top
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.69/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0)) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2637,plain,
% 2.69/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.69/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1957,c_1953]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_24,plain,
% 2.69/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_372,plain,
% 2.69/1.00      ( v2_tops_1(X0,sK0) != iProver_top
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.69/1.00      | r1_tarski(X0,k2_tops_1(sK0,X0)) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_374,plain,
% 2.69/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.69/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.69/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_372]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_13,plain,
% 2.69/1.00      ( v2_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | ~ l1_pre_topc(X1)
% 2.69/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_415,plain,
% 2.69/1.00      ( v2_tops_1(X0,X1)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.69/1.00      | sK0 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_416,plain,
% 2.69/1.00      ( v2_tops_1(X0,sK0)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_415]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_847,plain,
% 2.69/1.00      ( v2_tops_1(X0,sK0)
% 2.69/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.69/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 2.69/1.00      | sK1 != X0 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_416]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_848,plain,
% 2.69/1.00      ( v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_847]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_849,plain,
% 2.69/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.69/1.00      | v2_tops_1(sK1,sK0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2651,plain,
% 2.69/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_2637,c_21,c_24,c_74,c_78,c_374,c_388,c_403,c_507,
% 2.69/1.00                 c_849,c_2106]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4997,plain,
% 2.69/1.00      ( r1_tarski(sK1,k3_subset_1(sK1,k1_xboole_0)) = iProver_top ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_4898,c_2651]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_223,plain,
% 2.69/1.00      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 2.69/1.00      | ~ r1_tarski(X1,X0) ),
% 2.69/1.00      inference(bin_hyper_res,[status(thm)],[c_4,c_181]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1955,plain,
% 2.69/1.00      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 2.69/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3382,plain,
% 2.69/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.69/1.00      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1955,c_1958]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1961,plain,
% 2.69/1.00      ( X0 = X1
% 2.69/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.69/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3449,plain,
% 2.69/1.00      ( k3_subset_1(X0,X1) = X0
% 2.69/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.69/1.00      | r1_tarski(X0,k3_subset_1(X0,X1)) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3382,c_1961]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_5342,plain,
% 2.69/1.00      ( k3_subset_1(sK1,k1_xboole_0) = sK1
% 2.69/1.00      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_4997,c_3449]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_18,negated_conjecture,
% 2.69/1.00      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.69/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_182,plain,
% 2.69/1.00      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.69/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_9,plain,
% 2.69/1.00      ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
% 2.69/1.00      | v3_tops_1(X1,X0)
% 2.69/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/1.00      | ~ l1_pre_topc(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_340,plain,
% 2.69/1.00      ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
% 2.69/1.00      | v3_tops_1(X1,X0)
% 2.69/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/1.00      | sK0 != X0 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_341,plain,
% 2.69/1.00      ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
% 2.69/1.00      | v3_tops_1(X0,sK0)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_340]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_532,plain,
% 2.69/1.00      ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | k2_tops_1(sK0,sK1) != sK1
% 2.69/1.00      | sK1 != X0
% 2.69/1.00      | sK0 != sK0 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_182,c_341]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_533,plain,
% 2.69/1.00      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 2.69/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/1.00      | k2_tops_1(sK0,sK1) != sK1 ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_532]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_535,plain,
% 2.69/1.00      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 2.69/1.00      | k2_tops_1(sK0,sK1) != sK1 ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_533,c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1024,plain,
% 2.69/1.00      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 2.69/1.00      | k2_tops_1(sK0,sK1) != sK1 ),
% 2.69/1.00      inference(prop_impl,[status(thm)],[c_21,c_533]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1945,plain,
% 2.69/1.00      ( k2_tops_1(sK0,sK1) != sK1
% 2.69/1.00      | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1982,plain,
% 2.69/1.00      ( k2_tops_1(sK0,sK1) != sK1 | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_1945,c_319]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4999,plain,
% 2.69/1.00      ( k3_subset_1(sK1,k1_xboole_0) != sK1
% 2.69/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_4898,c_1982]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2102,plain,
% 2.69/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_1957,c_1949]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2140,plain,
% 2.69/1.00      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_2137,c_2102]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(contradiction,plain,
% 2.69/1.00      ( $false ),
% 2.69/1.00      inference(minisat,[status(thm)],[c_5342,c_4999,c_2140,c_2137,c_849]) ).
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  ------                               Statistics
% 2.69/1.00  
% 2.69/1.00  ------ General
% 2.69/1.00  
% 2.69/1.00  abstr_ref_over_cycles:                  0
% 2.69/1.00  abstr_ref_under_cycles:                 0
% 2.69/1.00  gc_basic_clause_elim:                   0
% 2.69/1.00  forced_gc_time:                         0
% 2.69/1.00  parsing_time:                           0.015
% 2.69/1.00  unif_index_cands_time:                  0.
% 2.69/1.00  unif_index_add_time:                    0.
% 2.69/1.00  orderings_time:                         0.
% 2.69/1.00  out_proof_time:                         0.01
% 2.69/1.00  total_time:                             0.171
% 2.69/1.00  num_of_symbols:                         50
% 2.69/1.00  num_of_terms:                           3331
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing
% 2.69/1.00  
% 2.69/1.00  num_of_splits:                          0
% 2.69/1.00  num_of_split_atoms:                     0
% 2.69/1.00  num_of_reused_defs:                     0
% 2.69/1.00  num_eq_ax_congr_red:                    22
% 2.69/1.00  num_of_sem_filtered_clauses:            1
% 2.69/1.00  num_of_subtypes:                        0
% 2.69/1.00  monotx_restored_types:                  0
% 2.69/1.00  sat_num_of_epr_types:                   0
% 2.69/1.00  sat_num_of_non_cyclic_types:            0
% 2.69/1.00  sat_guarded_non_collapsed_types:        0
% 2.69/1.00  num_pure_diseq_elim:                    0
% 2.69/1.00  simp_replaced_by:                       0
% 2.69/1.00  res_preprocessed:                       106
% 2.69/1.00  prep_upred:                             0
% 2.69/1.00  prep_unflattend:                        60
% 2.69/1.00  smt_new_axioms:                         0
% 2.69/1.00  pred_elim_cands:                        3
% 2.69/1.00  pred_elim:                              3
% 2.69/1.00  pred_elim_cl:                           3
% 2.69/1.00  pred_elim_cycles:                       5
% 2.69/1.00  merged_defs:                            16
% 2.69/1.00  merged_defs_ncl:                        0
% 2.69/1.00  bin_hyper_res:                          20
% 2.69/1.00  prep_cycles:                            4
% 2.69/1.00  pred_elim_time:                         0.015
% 2.69/1.00  splitting_time:                         0.
% 2.69/1.00  sem_filter_time:                        0.
% 2.69/1.00  monotx_time:                            0.
% 2.69/1.00  subtype_inf_time:                       0.
% 2.69/1.00  
% 2.69/1.00  ------ Problem properties
% 2.69/1.00  
% 2.69/1.00  clauses:                                19
% 2.69/1.00  conjectures:                            1
% 2.69/1.00  epr:                                    2
% 2.69/1.00  horn:                                   18
% 2.69/1.00  ground:                                 5
% 2.69/1.00  unary:                                  3
% 2.69/1.00  binary:                                 10
% 2.69/1.00  lits:                                   41
% 2.69/1.00  lits_eq:                                9
% 2.69/1.00  fd_pure:                                0
% 2.69/1.00  fd_pseudo:                              0
% 2.69/1.00  fd_cond:                                0
% 2.69/1.00  fd_pseudo_cond:                         1
% 2.69/1.00  ac_symbols:                             0
% 2.69/1.00  
% 2.69/1.00  ------ Propositional Solver
% 2.69/1.00  
% 2.69/1.00  prop_solver_calls:                      31
% 2.69/1.00  prop_fast_solver_calls:                 829
% 2.69/1.00  smt_solver_calls:                       0
% 2.69/1.00  smt_fast_solver_calls:                  0
% 2.69/1.00  prop_num_of_clauses:                    1524
% 2.69/1.00  prop_preprocess_simplified:             5208
% 2.69/1.00  prop_fo_subsumed:                       10
% 2.69/1.00  prop_solver_time:                       0.
% 2.69/1.00  smt_solver_time:                        0.
% 2.69/1.00  smt_fast_solver_time:                   0.
% 2.69/1.00  prop_fast_solver_time:                  0.
% 2.69/1.00  prop_unsat_core_time:                   0.
% 2.69/1.00  
% 2.69/1.00  ------ QBF
% 2.69/1.00  
% 2.69/1.00  qbf_q_res:                              0
% 2.69/1.00  qbf_num_tautologies:                    0
% 2.69/1.00  qbf_prep_cycles:                        0
% 2.69/1.00  
% 2.69/1.00  ------ BMC1
% 2.69/1.00  
% 2.69/1.00  bmc1_current_bound:                     -1
% 2.69/1.00  bmc1_last_solved_bound:                 -1
% 2.69/1.00  bmc1_unsat_core_size:                   -1
% 2.69/1.00  bmc1_unsat_core_parents_size:           -1
% 2.69/1.00  bmc1_merge_next_fun:                    0
% 2.69/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation
% 2.69/1.00  
% 2.69/1.00  inst_num_of_clauses:                    483
% 2.69/1.00  inst_num_in_passive:                    175
% 2.69/1.00  inst_num_in_active:                     298
% 2.69/1.00  inst_num_in_unprocessed:                10
% 2.69/1.00  inst_num_of_loops:                      320
% 2.69/1.00  inst_num_of_learning_restarts:          0
% 2.69/1.00  inst_num_moves_active_passive:          16
% 2.69/1.00  inst_lit_activity:                      0
% 2.69/1.00  inst_lit_activity_moves:                0
% 2.69/1.00  inst_num_tautologies:                   0
% 2.69/1.00  inst_num_prop_implied:                  0
% 2.69/1.00  inst_num_existing_simplified:           0
% 2.69/1.00  inst_num_eq_res_simplified:             0
% 2.69/1.00  inst_num_child_elim:                    0
% 2.69/1.00  inst_num_of_dismatching_blockings:      178
% 2.69/1.00  inst_num_of_non_proper_insts:           782
% 2.69/1.00  inst_num_of_duplicates:                 0
% 2.69/1.00  inst_inst_num_from_inst_to_res:         0
% 2.69/1.00  inst_dismatching_checking_time:         0.
% 2.69/1.00  
% 2.69/1.00  ------ Resolution
% 2.69/1.00  
% 2.69/1.00  res_num_of_clauses:                     0
% 2.69/1.00  res_num_in_passive:                     0
% 2.69/1.00  res_num_in_active:                      0
% 2.69/1.00  res_num_of_loops:                       110
% 2.69/1.00  res_forward_subset_subsumed:            61
% 2.69/1.00  res_backward_subset_subsumed:           2
% 2.69/1.00  res_forward_subsumed:                   0
% 2.69/1.00  res_backward_subsumed:                  0
% 2.69/1.00  res_forward_subsumption_resolution:     0
% 2.69/1.00  res_backward_subsumption_resolution:    0
% 2.69/1.00  res_clause_to_clause_subsumption:       430
% 2.69/1.00  res_orphan_elimination:                 0
% 2.69/1.00  res_tautology_del:                      127
% 2.69/1.00  res_num_eq_res_simplified:              0
% 2.69/1.00  res_num_sel_changes:                    0
% 2.69/1.00  res_moves_from_active_to_pass:          0
% 2.69/1.00  
% 2.69/1.00  ------ Superposition
% 2.69/1.00  
% 2.69/1.00  sup_time_total:                         0.
% 2.69/1.00  sup_time_generating:                    0.
% 2.69/1.00  sup_time_sim_full:                      0.
% 2.69/1.00  sup_time_sim_immed:                     0.
% 2.69/1.00  
% 2.69/1.00  sup_num_of_clauses:                     80
% 2.69/1.00  sup_num_in_active:                      52
% 2.69/1.00  sup_num_in_passive:                     28
% 2.69/1.00  sup_num_of_loops:                       62
% 2.69/1.00  sup_fw_superposition:                   53
% 2.69/1.00  sup_bw_superposition:                   35
% 2.69/1.00  sup_immediate_simplified:               19
% 2.69/1.00  sup_given_eliminated:                   1
% 2.69/1.00  comparisons_done:                       0
% 2.69/1.00  comparisons_avoided:                    0
% 2.69/1.00  
% 2.69/1.00  ------ Simplifications
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  sim_fw_subset_subsumed:                 7
% 2.69/1.00  sim_bw_subset_subsumed:                 1
% 2.69/1.00  sim_fw_subsumed:                        1
% 2.69/1.00  sim_bw_subsumed:                        0
% 2.69/1.00  sim_fw_subsumption_res:                 1
% 2.69/1.00  sim_bw_subsumption_res:                 0
% 2.69/1.00  sim_tautology_del:                      7
% 2.69/1.00  sim_eq_tautology_del:                   1
% 2.69/1.00  sim_eq_res_simp:                        0
% 2.69/1.00  sim_fw_demodulated:                     8
% 2.69/1.00  sim_bw_demodulated:                     20
% 2.69/1.00  sim_light_normalised:                   8
% 2.69/1.00  sim_joinable_taut:                      0
% 2.69/1.00  sim_joinable_simp:                      0
% 2.69/1.00  sim_ac_normalised:                      0
% 2.69/1.00  sim_smt_subsumption:                    0
% 2.69/1.00  
%------------------------------------------------------------------------------
