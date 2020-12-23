%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:37 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  106 (1009 expanded)
%              Number of clauses        :   71 ( 360 expanded)
%              Number of leaves         :    9 ( 209 expanded)
%              Depth                    :   20
%              Number of atoms          :  312 (3982 expanded)
%              Number of equality atoms :  132 ( 503 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
            <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v6_tops_1(X1,X0)
          <~> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v6_tops_1(X1,X0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v6_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v6_tops_1(X1,X0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v6_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v6_tops_1(X1,X0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v6_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | ~ v6_tops_1(sK1,X0) )
        & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | v6_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v6_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v6_tops_1(X1,sK0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v6_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v6_tops_1(sK1,sK0) )
    & ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v6_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_144,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_477,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_144])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_152,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_469,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39))) = iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_153,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
    | k3_subset_1(X0_42,k3_subset_1(X0_42,X0_40)) = X0_40 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_468,plain,
    ( k3_subset_1(X0_42,k3_subset_1(X0_42,X0_40)) = X0_40
    | m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_153])).

cnf(c_816,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,X0_40))) = k2_pre_topc(X0_39,X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_469,c_468])).

cnf(c_2800,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_477,c_816])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_179,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_595,plain,
    ( ~ m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39)))
    | k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,X0_40))) = k2_pre_topc(X0_39,X0_40) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_597,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_3013,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2800,c_11,c_10,c_179,c_597])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_154,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
    | m1_subset_1(k3_subset_1(X0_42,X0_40),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_467,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_42,X0_40),k1_zfmisc_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_3016,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3013,c_467])).

cnf(c_12,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_178,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39))) = iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_180,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_3019,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3016,c_12,c_13,c_180])).

cnf(c_2802,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40)))) = k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_467,c_816])).

cnf(c_13442,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3019,c_2802])).

cnf(c_9,negated_conjecture,
    ( v6_tops_1(sK1,sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_145,negated_conjecture,
    ( v6_tops_1(sK1,sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_476,plain,
    ( v6_tops_1(sK1,sK0) = iProver_top
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_5,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_149,plain,
    ( ~ v5_tops_1(X0_40,X0_39)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) = X0_40 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_472,plain,
    ( k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) = X0_40
    | v5_tops_1(X0_40,X0_39) != iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_1029,plain,
    ( k2_pre_topc(X0_39,k1_tops_1(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k3_subset_1(u1_struct_0(X0_39),X0_40)
    | v5_tops_1(k3_subset_1(u1_struct_0(X0_39),X0_40),X0_39) != iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_467,c_472])).

cnf(c_10055,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | v6_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_1029])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_151,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k1_tops_1(X0_39,X0_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_470,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k1_tops_1(X0_39,X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_913,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),X0_40)))) = k1_tops_1(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_467,c_470])).

cnf(c_5922,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_477,c_913])).

cnf(c_751,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_477,c_468])).

cnf(c_5976,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5922,c_751])).

cnf(c_6988,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5976,c_12])).

cnf(c_10238,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | v6_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10055,c_6988])).

cnf(c_10959,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | v6_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10238,c_12,c_13])).

cnf(c_7,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_147,plain,
    ( ~ v6_tops_1(X0_40,X0_39)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) = X0_40 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_474,plain,
    ( k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) = X0_40
    | v6_tops_1(X0_40,X0_39) != iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_147])).

cnf(c_1730,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | v6_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_477,c_474])).

cnf(c_1954,plain,
    ( v6_tops_1(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1730,c_12])).

cnf(c_1955,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | v6_tops_1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1954])).

cnf(c_10965,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_10959,c_1955])).

cnf(c_3027,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3019,c_470])).

cnf(c_912,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,X0_40)))) = k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_469,c_470])).

cnf(c_932,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_3240,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3027,c_12,c_13,c_932])).

cnf(c_11460,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_10965,c_3240])).

cnf(c_11463,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_11460,c_751])).

cnf(c_11478,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = sK1 ),
    inference(demodulation,[status(thm)],[c_11463,c_3240])).

cnf(c_13476,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13442,c_11478])).

cnf(c_4,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_150,plain,
    ( v5_tops_1(X0_40,X0_39)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) != X0_40 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_471,plain,
    ( k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) != X0_40
    | v5_tops_1(X0_40,X0_39) = iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_6991,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),sK1)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6988,c_471])).

cnf(c_6992,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6991])).

cnf(c_584,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_6,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_148,plain,
    ( v6_tops_1(X0_40,X0_39)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) != X0_40 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_191,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_8,negated_conjecture,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13476,c_11463,c_6992,c_584,c_191,c_8,c_10,c_12,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.89/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/1.00  
% 3.89/1.00  ------  iProver source info
% 3.89/1.00  
% 3.89/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.89/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/1.00  git: non_committed_changes: false
% 3.89/1.00  git: last_make_outside_of_git: false
% 3.89/1.00  
% 3.89/1.00  ------ 
% 3.89/1.00  ------ Parsing...
% 3.89/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.00  ------ Proving...
% 3.89/1.00  ------ Problem Properties 
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  clauses                                 12
% 3.89/1.00  conjectures                             4
% 3.89/1.00  EPR                                     1
% 3.89/1.00  Horn                                    11
% 3.89/1.00  unary                                   2
% 3.89/1.00  binary                                  4
% 3.89/1.00  lits                                    32
% 3.89/1.00  lits eq                                 6
% 3.89/1.00  fd_pure                                 0
% 3.89/1.00  fd_pseudo                               0
% 3.89/1.00  fd_cond                                 0
% 3.89/1.00  fd_pseudo_cond                          0
% 3.89/1.00  AC symbols                              0
% 3.89/1.00  
% 3.89/1.00  ------ Input Options Time Limit: Unbounded
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  ------ 
% 3.89/1.00  Current options:
% 3.89/1.00  ------ 
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  ------ Proving...
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  % SZS status Theorem for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  fof(f7,conjecture,(
% 3.89/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f8,negated_conjecture,(
% 3.89/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.89/1.00    inference(negated_conjecture,[],[f7])).
% 3.89/1.00  
% 3.89/1.00  fof(f16,plain,(
% 3.89/1.00    ? [X0] : (? [X1] : ((v6_tops_1(X1,X0) <~> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.89/1.00    inference(ennf_transformation,[],[f8])).
% 3.89/1.00  
% 3.89/1.00  fof(f19,plain,(
% 3.89/1.00    ? [X0] : (? [X1] : (((~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v6_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.89/1.00    inference(nnf_transformation,[],[f16])).
% 3.89/1.00  
% 3.89/1.00  fof(f20,plain,(
% 3.89/1.00    ? [X0] : (? [X1] : ((~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v6_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.89/1.00    inference(flattening,[],[f19])).
% 3.89/1.00  
% 3.89/1.00  fof(f22,plain,(
% 3.89/1.00    ( ! [X0] : (? [X1] : ((~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v6_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v5_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0) | ~v6_tops_1(sK1,X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0) | v6_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.89/1.00    introduced(choice_axiom,[])).
% 3.89/1.00  
% 3.89/1.00  fof(f21,plain,(
% 3.89/1.00    ? [X0] : (? [X1] : ((~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v6_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v6_tops_1(X1,sK0)) & (v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v6_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.89/1.00    introduced(choice_axiom,[])).
% 3.89/1.00  
% 3.89/1.00  fof(f23,plain,(
% 3.89/1.00    ((~v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v6_tops_1(sK1,sK0)) & (v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v6_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.89/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 3.89/1.00  
% 3.89/1.00  fof(f33,plain,(
% 3.89/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.89/1.00    inference(cnf_transformation,[],[f23])).
% 3.89/1.00  
% 3.89/1.00  fof(f3,axiom,(
% 3.89/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f11,plain,(
% 3.89/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.89/1.00    inference(ennf_transformation,[],[f3])).
% 3.89/1.00  
% 3.89/1.00  fof(f12,plain,(
% 3.89/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.89/1.00    inference(flattening,[],[f11])).
% 3.89/1.00  
% 3.89/1.00  fof(f26,plain,(
% 3.89/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f12])).
% 3.89/1.00  
% 3.89/1.00  fof(f2,axiom,(
% 3.89/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f10,plain,(
% 3.89/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.89/1.00    inference(ennf_transformation,[],[f2])).
% 3.89/1.00  
% 3.89/1.00  fof(f25,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.89/1.00    inference(cnf_transformation,[],[f10])).
% 3.89/1.00  
% 3.89/1.00  fof(f32,plain,(
% 3.89/1.00    l1_pre_topc(sK0)),
% 3.89/1.00    inference(cnf_transformation,[],[f23])).
% 3.89/1.00  
% 3.89/1.00  fof(f1,axiom,(
% 3.89/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f9,plain,(
% 3.89/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.89/1.00    inference(ennf_transformation,[],[f1])).
% 3.89/1.00  
% 3.89/1.00  fof(f24,plain,(
% 3.89/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.89/1.00    inference(cnf_transformation,[],[f9])).
% 3.89/1.00  
% 3.89/1.00  fof(f34,plain,(
% 3.89/1.00    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v6_tops_1(sK1,sK0)),
% 3.89/1.00    inference(cnf_transformation,[],[f23])).
% 3.89/1.00  
% 3.89/1.00  fof(f5,axiom,(
% 3.89/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f14,plain,(
% 3.89/1.00    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/1.00    inference(ennf_transformation,[],[f5])).
% 3.89/1.00  
% 3.89/1.00  fof(f17,plain,(
% 3.89/1.00    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/1.00    inference(nnf_transformation,[],[f14])).
% 3.89/1.00  
% 3.89/1.00  fof(f28,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f17])).
% 3.89/1.00  
% 3.89/1.00  fof(f4,axiom,(
% 3.89/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f13,plain,(
% 3.89/1.00    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/1.00    inference(ennf_transformation,[],[f4])).
% 3.89/1.00  
% 3.89/1.00  fof(f27,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f13])).
% 3.89/1.00  
% 3.89/1.00  fof(f6,axiom,(
% 3.89/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 3.89/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f15,plain,(
% 3.89/1.00    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/1.00    inference(ennf_transformation,[],[f6])).
% 3.89/1.00  
% 3.89/1.00  fof(f18,plain,(
% 3.89/1.00    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/1.00    inference(nnf_transformation,[],[f15])).
% 3.89/1.00  
% 3.89/1.00  fof(f30,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f18])).
% 3.89/1.00  
% 3.89/1.00  fof(f29,plain,(
% 3.89/1.00    ( ! [X0,X1] : (v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f17])).
% 3.89/1.00  
% 3.89/1.00  fof(f31,plain,(
% 3.89/1.00    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f18])).
% 3.89/1.00  
% 3.89/1.00  fof(f35,plain,(
% 3.89/1.00    ~v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v6_tops_1(sK1,sK0)),
% 3.89/1.00    inference(cnf_transformation,[],[f23])).
% 3.89/1.00  
% 3.89/1.00  cnf(c_10,negated_conjecture,
% 3.89/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.89/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_144,negated_conjecture,
% 3.89/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_477,plain,
% 3.89/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_144]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2,plain,
% 3.89/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/1.00      | ~ l1_pre_topc(X1) ),
% 3.89/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_152,plain,
% 3.89/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
% 3.89/1.00      | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39)))
% 3.89/1.00      | ~ l1_pre_topc(X0_39) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_469,plain,
% 3.89/1.00      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39))) = iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_152]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1,plain,
% 3.89/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.89/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_153,plain,
% 3.89/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
% 3.89/1.00      | k3_subset_1(X0_42,k3_subset_1(X0_42,X0_40)) = X0_40 ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_468,plain,
% 3.89/1.00      ( k3_subset_1(X0_42,k3_subset_1(X0_42,X0_40)) = X0_40
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_153]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_816,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,X0_40))) = k2_pre_topc(X0_39,X0_40)
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_469,c_468]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2800,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_477,c_816]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11,negated_conjecture,
% 3.89/1.00      ( l1_pre_topc(sK0) ),
% 3.89/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_179,plain,
% 3.89/1.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.89/1.00      | ~ l1_pre_topc(sK0) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_152]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_595,plain,
% 3.89/1.00      ( ~ m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39)))
% 3.89/1.00      | k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,X0_40))) = k2_pre_topc(X0_39,X0_40) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_153]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_597,plain,
% 3.89/1.00      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.89/1.00      | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_595]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3013,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_2800,c_11,c_10,c_179,c_597]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_0,plain,
% 3.89/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.89/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.89/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_154,plain,
% 3.89/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
% 3.89/1.00      | m1_subset_1(k3_subset_1(X0_42,X0_40),k1_zfmisc_1(X0_42)) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_467,plain,
% 3.89/1.00      ( m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
% 3.89/1.00      | m1_subset_1(k3_subset_1(X0_42,X0_40),k1_zfmisc_1(X0_42)) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3016,plain,
% 3.89/1.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.89/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_3013,c_467]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_12,plain,
% 3.89/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_13,plain,
% 3.89/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_178,plain,
% 3.89/1.00      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39))) = iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_152]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_180,plain,
% 3.89/1.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.89/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_178]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3019,plain,
% 3.89/1.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_3016,c_12,c_13,c_180]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2802,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40)))) = k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_467,c_816]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_13442,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_3019,c_2802]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_9,negated_conjecture,
% 3.89/1.00      ( v6_tops_1(sK1,sK0)
% 3.89/1.00      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 3.89/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_145,negated_conjecture,
% 3.89/1.00      ( v6_tops_1(sK1,sK0)
% 3.89/1.00      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_476,plain,
% 3.89/1.00      ( v6_tops_1(sK1,sK0) = iProver_top
% 3.89/1.00      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_145]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_5,plain,
% 3.89/1.00      ( ~ v5_tops_1(X0,X1)
% 3.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/1.00      | ~ l1_pre_topc(X1)
% 3.89/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_149,plain,
% 3.89/1.00      ( ~ v5_tops_1(X0_40,X0_39)
% 3.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
% 3.89/1.00      | ~ l1_pre_topc(X0_39)
% 3.89/1.00      | k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) = X0_40 ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_472,plain,
% 3.89/1.00      ( k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) = X0_40
% 3.89/1.00      | v5_tops_1(X0_40,X0_39) != iProver_top
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_149]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1029,plain,
% 3.89/1.00      ( k2_pre_topc(X0_39,k1_tops_1(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k3_subset_1(u1_struct_0(X0_39),X0_40)
% 3.89/1.00      | v5_tops_1(k3_subset_1(u1_struct_0(X0_39),X0_40),X0_39) != iProver_top
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_467,c_472]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_10055,plain,
% 3.89/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
% 3.89/1.00      | v6_tops_1(sK1,sK0) = iProver_top
% 3.89/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_476,c_1029]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3,plain,
% 3.89/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/1.00      | ~ l1_pre_topc(X1)
% 3.89/1.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.89/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_151,plain,
% 3.89/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
% 3.89/1.00      | ~ l1_pre_topc(X0_39)
% 3.89/1.00      | k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k1_tops_1(X0_39,X0_40) ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_470,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k1_tops_1(X0_39,X0_40)
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_913,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),X0_40)))) = k1_tops_1(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_467,c_470]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_5922,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_477,c_913]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_751,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_477,c_468]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_5976,plain,
% 3.89/1.00      ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(light_normalisation,[status(thm)],[c_5922,c_751]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6988,plain,
% 3.89/1.00      ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_5976,c_12]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_10238,plain,
% 3.89/1.00      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
% 3.89/1.00      | v6_tops_1(sK1,sK0) = iProver_top
% 3.89/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(light_normalisation,[status(thm)],[c_10055,c_6988]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_10959,plain,
% 3.89/1.00      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
% 3.89/1.00      | v6_tops_1(sK1,sK0) = iProver_top ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_10238,c_12,c_13]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_7,plain,
% 3.89/1.00      ( ~ v6_tops_1(X0,X1)
% 3.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/1.00      | ~ l1_pre_topc(X1)
% 3.89/1.00      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_147,plain,
% 3.89/1.00      ( ~ v6_tops_1(X0_40,X0_39)
% 3.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
% 3.89/1.00      | ~ l1_pre_topc(X0_39)
% 3.89/1.00      | k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) = X0_40 ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_474,plain,
% 3.89/1.00      ( k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) = X0_40
% 3.89/1.00      | v6_tops_1(X0_40,X0_39) != iProver_top
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_147]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1730,plain,
% 3.89/1.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
% 3.89/1.00      | v6_tops_1(sK1,sK0) != iProver_top
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_477,c_474]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1954,plain,
% 3.89/1.00      ( v6_tops_1(sK1,sK0) != iProver_top
% 3.89/1.00      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_1730,c_12]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1955,plain,
% 3.89/1.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
% 3.89/1.00      | v6_tops_1(sK1,sK0) != iProver_top ),
% 3.89/1.00      inference(renaming,[status(thm)],[c_1954]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_10965,plain,
% 3.89/1.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
% 3.89/1.00      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_10959,c_1955]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3027,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_3019,c_470]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_912,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,X0_40)))) = k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40))
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_469,c_470]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_932,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
% 3.89/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_912]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3240,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_3027,c_12,c_13,c_932]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11460,plain,
% 3.89/1.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
% 3.89/1.00      | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_10965,c_3240]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11463,plain,
% 3.89/1.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
% 3.89/1.00      inference(light_normalisation,[status(thm)],[c_11460,c_751]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11478,plain,
% 3.89/1.00      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = sK1 ),
% 3.89/1.00      inference(demodulation,[status(thm)],[c_11463,c_3240]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_13476,plain,
% 3.89/1.00      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(light_normalisation,[status(thm)],[c_13442,c_11478]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4,plain,
% 3.89/1.00      ( v5_tops_1(X0,X1)
% 3.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/1.00      | ~ l1_pre_topc(X1)
% 3.89/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_150,plain,
% 3.89/1.00      ( v5_tops_1(X0_40,X0_39)
% 3.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
% 3.89/1.00      | ~ l1_pre_topc(X0_39)
% 3.89/1.00      | k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) != X0_40 ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_471,plain,
% 3.89/1.00      ( k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) != X0_40
% 3.89/1.00      | v5_tops_1(X0_40,X0_39) = iProver_top
% 3.89/1.00      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
% 3.89/1.00      | l1_pre_topc(X0_39) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6991,plain,
% 3.89/1.00      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),sK1)
% 3.89/1.00      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
% 3.89/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_6988,c_471]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6992,plain,
% 3.89/1.00      ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 3.89/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.89/1.00      | ~ l1_pre_topc(sK0)
% 3.89/1.00      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 3.89/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6991]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_584,plain,
% 3.89/1.00      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_154]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6,plain,
% 3.89/1.00      ( v6_tops_1(X0,X1)
% 3.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/1.00      | ~ l1_pre_topc(X1)
% 3.89/1.00      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_148,plain,
% 3.89/1.00      ( v6_tops_1(X0_40,X0_39)
% 3.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
% 3.89/1.00      | ~ l1_pre_topc(X0_39)
% 3.89/1.00      | k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) != X0_40 ),
% 3.89/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_191,plain,
% 3.89/1.00      ( v6_tops_1(sK1,sK0)
% 3.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.89/1.00      | ~ l1_pre_topc(sK0)
% 3.89/1.00      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != sK1 ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_148]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_8,negated_conjecture,
% 3.89/1.00      ( ~ v6_tops_1(sK1,sK0)
% 3.89/1.00      | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 3.89/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(contradiction,plain,
% 3.89/1.00      ( $false ),
% 3.89/1.00      inference(minisat,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_13476,c_11463,c_6992,c_584,c_191,c_8,c_10,c_12,c_11]) ).
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  ------                               Statistics
% 3.89/1.00  
% 3.89/1.00  ------ Selected
% 3.89/1.00  
% 3.89/1.00  total_time:                             0.429
% 3.89/1.00  
%------------------------------------------------------------------------------
