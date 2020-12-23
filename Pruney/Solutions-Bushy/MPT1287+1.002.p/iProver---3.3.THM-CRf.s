%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1287+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:20 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 368 expanded)
%              Number of clauses        :   79 ( 129 expanded)
%              Number of leaves         :   12 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          :  341 (1807 expanded)
%              Number of equality atoms :   91 ( 125 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v6_tops_1(X2,X0)
                  & v6_tops_1(X1,X0) )
               => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v6_tops_1(X2,X0)
                    & v6_tops_1(X1,X0) )
                 => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v6_tops_1(X2,X0)
          & v6_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v6_tops_1(sK2,X0)
        & v6_tops_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v6_tops_1(X2,X0)
            & v6_tops_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v6_tops_1(X2,X0)
                & v6_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v6_tops_1(X2,sK0)
              & v6_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v6_tops_1(sK2,sK0)
    & v6_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26,f25,f24])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v5_tops_1(X2,X0)
                  & v5_tops_1(X1,X0) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v5_tops_1(X2,X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_394,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_630,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | m1_subset_1(k3_subset_1(X0_45,X0_44),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_625,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_45,X0_44),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_395,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_629,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X0_45))
    | k4_subset_1(X0_45,X0_44,X1_44) = k2_xboole_0(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_627,plain,
    ( k4_subset_1(X0_45,X0_44,X1_44) = k2_xboole_0(X0_44,X1_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_2524,plain,
    ( k4_subset_1(X0_45,X0_44,k3_subset_1(X0_45,X1_44)) = k2_xboole_0(X0_44,k3_subset_1(X0_45,X1_44))
    | m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_627])).

cnf(c_21335,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK2)) = k2_xboole_0(X0_44,k3_subset_1(u1_struct_0(sK0),sK2))
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_2524])).

cnf(c_23013,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_44),k3_subset_1(u1_struct_0(sK0),sK2)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),X0_44),k3_subset_1(u1_struct_0(sK0),sK2))
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_21335])).

cnf(c_27528,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_630,c_23013])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | k9_subset_1(X0_45,X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_628,plain,
    ( k9_subset_1(X0_45,X0_44,X1_44) = k3_xboole_0(X0_44,X1_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1680,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_44,sK2) = k3_xboole_0(X0_44,sK2) ),
    inference(superposition,[status(thm)],[c_629,c_628])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_626,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_2088,plain,
    ( m1_subset_1(k3_xboole_0(X0_44,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1680,c_626])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5351,plain,
    ( m1_subset_1(k3_xboole_0(X0_44,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2088,c_20])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | k4_xboole_0(X0_45,X0_44) = k3_subset_1(X0_45,X0_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_624,plain,
    ( k4_xboole_0(X0_45,X0_44) = k3_subset_1(X0_45,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_5360,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k3_xboole_0(X0_44,sK2)) = k3_subset_1(u1_struct_0(sK0),k3_xboole_0(X0_44,sK2)) ),
    inference(superposition,[status(thm)],[c_5351,c_624])).

cnf(c_1011,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_630,c_624])).

cnf(c_1010,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_629,c_624])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_396,plain,
    ( k2_xboole_0(k4_xboole_0(X0_45,X0_44),k4_xboole_0(X0_45,X1_44)) = k4_xboole_0(X0_45,k3_xboole_0(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1217,plain,
    ( k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),X0_44),k3_subset_1(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k3_xboole_0(X0_44,sK2)) ),
    inference(superposition,[status(thm)],[c_1010,c_396])).

cnf(c_1448,plain,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1011,c_1217])).

cnf(c_9245,plain,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_5360,c_1448])).

cnf(c_27552,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_27528,c_9245])).

cnf(c_8,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ v5_tops_1(X2,X1)
    | v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_174,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ v5_tops_1(X2,X1)
    | v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_175,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ v5_tops_1(X1,sK0)
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_179,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
    | ~ v5_tops_1(X1,sK0)
    | ~ v5_tops_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_175,c_15])).

cnf(c_180,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ v5_tops_1(X1,sK0)
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_393,plain,
    ( ~ v5_tops_1(X0_44,sK0)
    | ~ v5_tops_1(X1_44,sK0)
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0_44,X1_44),sK0)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_180])).

cnf(c_631,plain,
    ( v5_tops_1(X0_44,sK0) != iProver_top
    | v5_tops_1(X1_44,sK0) != iProver_top
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0_44,X1_44),sK0) = iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_27568,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,sK2)),sK0) = iProver_top
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27552,c_631])).

cnf(c_10,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v6_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_222,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v6_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_223,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_260,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_223])).

cnf(c_261,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_392,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_261])).

cnf(c_632,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_262,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_727,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_44,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_728,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_44,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_730,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_938,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_20,c_262,c_730])).

cnf(c_2078,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1680,c_938])).

cnf(c_724,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_725,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_721,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_722,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_12,negated_conjecture,
    ( v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v6_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_207,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v6_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_208,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_281,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_208])).

cnf(c_282,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_283,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_11,negated_conjecture,
    ( v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_270,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_208])).

cnf(c_271,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_272,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27568,c_2078,c_725,c_722,c_283,c_272,c_20,c_19])).


%------------------------------------------------------------------------------
