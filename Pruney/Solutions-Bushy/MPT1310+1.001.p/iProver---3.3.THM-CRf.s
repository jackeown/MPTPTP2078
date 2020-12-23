%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1310+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:25 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 656 expanded)
%              Number of clauses        :   96 ( 232 expanded)
%              Number of leaves         :   21 ( 161 expanded)
%              Depth                    :   23
%              Number of atoms          :  458 (3009 expanded)
%              Number of equality atoms :  114 ( 217 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ( v1_finset_1(X1)
              & v2_tops_2(X1,X0) )
           => v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( ( v1_finset_1(X1)
                & v2_tops_2(X1,X0) )
             => v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),sK1),X0)
        & v1_finset_1(sK1)
        & v2_tops_2(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
            & v1_finset_1(X1)
            & v2_tops_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),X1),sK0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    & v1_finset_1(sK1)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f34,f33])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ( v1_finset_1(X1)
              & v1_tops_2(X1,X0) )
           => v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_finset_1(X1)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_finset_1(X1)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v1_finset_1(X1)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
              | ~ v1_finset_1(X1) )
            & ( v1_finset_1(X1)
              | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
      | ~ v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_576,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1482,plain,
    ( X0_48 != X1_48
    | X0_48 = k5_setfam_1(u1_struct_0(sK0),X2_48)
    | k5_setfam_1(u1_struct_0(sK0),X2_48) != X1_48 ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_1483,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_566,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_784,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
    | k5_setfam_1(X0_49,X0_48) = k3_tarski(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_781,plain,
    ( k5_setfam_1(X0_49,X0_48) = k3_tarski(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X0_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_1149,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_784,c_781])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_231,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v4_pre_topc(k1_xboole_0,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_253,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v4_pre_topc(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_231,c_20])).

cnf(c_254,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_233,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_256,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_20,c_19,c_233])).

cnf(c_257,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(renaming,[status(thm)],[c_256])).

cnf(c_410,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_setfam_1(u1_struct_0(sK0),sK1) != k1_xboole_0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_257])).

cnf(c_498,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_setfam_1(u1_struct_0(sK0),sK1) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_410])).

cnf(c_562,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_setfam_1(u1_struct_0(sK0),sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_498])).

cnf(c_788,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_1283,plain,
    ( k3_tarski(sK1) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1149,c_788])).

cnf(c_14,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_568,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k3_subset_1(X1,k5_setfam_1(X1,X0)) = k6_setfam_1(X1,k7_setfam_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
    | k3_subset_1(X0_49,k5_setfam_1(X0_49,X0_48)) = k6_setfam_1(X0_49,k7_setfam_1(X0_49,X0_48))
    | k1_xboole_0 = X0_48 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_782,plain,
    ( k3_subset_1(X0_49,k5_setfam_1(X0_49,X0_48)) = k6_setfam_1(X0_49,k7_setfam_1(X0_49,X0_48))
    | k1_xboole_0 = X0_48
    | m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X0_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_1219,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) = k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_784,c_782])).

cnf(c_16,negated_conjecture,
    ( v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v4_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v1_finset_1(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_267,plain,
    ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v1_finset_1(X1)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_268,plain,
    ( v3_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0)
    | ~ v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(X0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_272,plain,
    ( ~ v1_finset_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(X0,sK0)
    | v3_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_19])).

cnf(c_273,plain,
    ( v3_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0)
    | ~ v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(X0) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_10,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_346,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_347,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_349,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_19,c_18])).

cnf(c_359,plain,
    ( v3_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(X0)
    | k7_setfam_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_273,c_349])).

cnf(c_360,plain,
    ( v3_pre_topc(k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(X0,X1)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(X1)
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(X1),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_360])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(X0,sK0)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_382,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_19])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(X0,sK0)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(sK0),X0)
    | k5_setfam_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_383])).

cnf(c_423,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_565,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_finset_1(X0)
    | v1_finset_1(k7_setfam_1(u1_struct_0(X1),X0))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_finset_1(X0)
    | v1_finset_1(k7_setfam_1(u1_struct_0(X1),X0))
    | ~ l1_pre_topc(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_3])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_finset_1(X0)
    | v1_finset_1(k7_setfam_1(u1_struct_0(X1),X0))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_finset_1(X0)
    | v1_finset_1(k7_setfam_1(u1_struct_0(X1),X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_318,c_19])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(X0)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X0)) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(X0_48)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X0_48)) ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_859,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ v1_finset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
    | m1_subset_1(k7_setfam_1(X0_49,X0_48),k1_zfmisc_1(k1_zfmisc_1(X0_49))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_870,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
    | m1_subset_1(k5_setfam_1(X0_49,X0_48),k1_zfmisc_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_873,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_577,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_906,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) != X0_51
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != X0_51
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_1160,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) != k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1))
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_575,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1279,plain,
    ( k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_1294,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1219,c_18,c_16,c_565,c_859,c_870,c_873,c_1160,c_1279])).

cnf(c_1420,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1283,c_568,c_1294])).

cnf(c_1421,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1420])).

cnf(c_1297,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1294,c_1149])).

cnf(c_1308,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1297,c_568])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0_48,X0_49)
    | m1_subset_1(X1_48,X0_49)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1262,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),X1_48),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0_48 != k5_setfam_1(u1_struct_0(sK0),X1_48) ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1263,plain,
    ( X0_48 != k5_setfam_1(u1_struct_0(sK0),X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k5_setfam_1(u1_struct_0(sK0),X1_48),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_1265,plain,
    ( k1_xboole_0 != k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | m1_subset_1(k5_setfam_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_909,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
    | k3_subset_1(X0_49,k5_setfam_1(X0_49,sK1)) = k6_setfam_1(X0_49,k7_setfam_1(X0_49,sK1))
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_1059,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) = k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_909])).

cnf(c_579,plain,
    ( X0_48 != X1_48
    | k5_setfam_1(X0_49,X0_48) = k5_setfam_1(X0_49,X1_48) ),
    theory(equality)).

cnf(c_1045,plain,
    ( X0_48 != sK1
    | k5_setfam_1(u1_struct_0(sK0),X0_48) = k5_setfam_1(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_1050,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),sK1)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_919,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0_48 != k5_setfam_1(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1044,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),X0_48),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_setfam_1(u1_struct_0(sK0),X0_48) != k5_setfam_1(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_1046,plain,
    ( k5_setfam_1(u1_struct_0(sK0),X0_48) != k5_setfam_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(k5_setfam_1(u1_struct_0(sK0),X0_48),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_1048,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) != k5_setfam_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k5_setfam_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_874,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_574,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_593,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1483,c_1421,c_1308,c_1279,c_1265,c_1160,c_1059,c_1050,c_1048,c_874,c_873,c_870,c_859,c_565,c_593,c_16,c_23,c_18])).


%------------------------------------------------------------------------------
