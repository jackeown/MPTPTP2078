%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:51 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 355 expanded)
%              Number of clauses        :   60 (  95 expanded)
%              Number of leaves         :   10 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  349 (2073 expanded)
%              Number of equality atoms :   83 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0) )
           => ( v5_tops_1(X1,X0)
            <=> v6_tops_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v3_pre_topc(X1,X0) )
             => ( v5_tops_1(X1,X0)
              <=> v6_tops_1(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v6_tops_1(sK1,X0)
          | ~ v5_tops_1(sK1,X0) )
        & ( v6_tops_1(sK1,X0)
          | v5_tops_1(sK1,X0) )
        & v4_pre_topc(sK1,X0)
        & v3_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v6_tops_1(X1,X0)
              | ~ v5_tops_1(X1,X0) )
            & ( v6_tops_1(X1,X0)
              | v5_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v6_tops_1(X1,sK0)
            | ~ v5_tops_1(X1,sK0) )
          & ( v6_tops_1(X1,sK0)
            | v5_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ v6_tops_1(sK1,sK0)
      | ~ v5_tops_1(sK1,sK0) )
    & ( v6_tops_1(sK1,sK0)
      | v5_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f43,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_274,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_275,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_277,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_15,c_14])).

cnf(c_611,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_933,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_927,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_316,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_317,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_608,plain,
    ( ~ v3_pre_topc(X0_41,sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0_41))) = k2_pre_topc(sK0,X0_41) ),
    inference(subtyping,[status(esa)],[c_317])).

cnf(c_935,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0_41))) = k2_pre_topc(sK0,X0_41)
    | v3_pre_topc(X0_41,sK0) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_1336,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_41)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_41))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0_41),sK0) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_935])).

cnf(c_1666,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_1336])).

cnf(c_614,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_930,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_928,plain,
    ( k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_1162,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_930,c_928])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_256,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | X2 != X1
    | X3 != X0
    | k2_pre_topc(X3,X2) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_2])).

cnf(c_257,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_301,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k2_pre_topc(X0,X1) = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_257,c_15])).

cnf(c_302,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_609,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0_41),sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0_41) = X0_41 ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_934,plain,
    ( k2_pre_topc(sK0,X0_41) = X0_41
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0_41),sK0) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_1242,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1)
    | v3_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_934])).

cnf(c_17,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1022,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_1023,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_1524,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1242,c_17,c_18,c_1023])).

cnf(c_1674,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1666,c_1524])).

cnf(c_1335,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_935])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_286,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_288,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_15,c_14])).

cnf(c_610,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(subtyping,[status(esa)],[c_288])).

cnf(c_1345,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1335,c_610])).

cnf(c_3,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_346,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_347,plain,
    ( v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_606,plain,
    ( v5_tops_1(X0_41,sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0_41)) != X0_41 ),
    inference(subtyping,[status(esa)],[c_347])).

cnf(c_1071,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_654,plain,
    ( v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_5,plain,
    ( v6_tops_1(X0,X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,negated_conjecture,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_120,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(sK1,sK0) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_221,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_120])).

cnf(c_222,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_224,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v5_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_15,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1674,c_1345,c_1071,c_1022,c_654,c_224,c_18,c_17,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.67/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.00  
% 1.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.67/1.00  
% 1.67/1.00  ------  iProver source info
% 1.67/1.00  
% 1.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.67/1.00  git: non_committed_changes: false
% 1.67/1.00  git: last_make_outside_of_git: false
% 1.67/1.00  
% 1.67/1.00  ------ 
% 1.67/1.00  
% 1.67/1.00  ------ Input Options
% 1.67/1.00  
% 1.67/1.00  --out_options                           all
% 1.67/1.00  --tptp_safe_out                         true
% 1.67/1.00  --problem_path                          ""
% 1.67/1.00  --include_path                          ""
% 1.67/1.00  --clausifier                            res/vclausify_rel
% 1.67/1.00  --clausifier_options                    --mode clausify
% 1.67/1.00  --stdin                                 false
% 1.67/1.00  --stats_out                             all
% 1.67/1.00  
% 1.67/1.00  ------ General Options
% 1.67/1.00  
% 1.67/1.00  --fof                                   false
% 1.67/1.00  --time_out_real                         305.
% 1.67/1.00  --time_out_virtual                      -1.
% 1.67/1.00  --symbol_type_check                     false
% 1.67/1.00  --clausify_out                          false
% 1.67/1.00  --sig_cnt_out                           false
% 1.67/1.00  --trig_cnt_out                          false
% 1.67/1.00  --trig_cnt_out_tolerance                1.
% 1.67/1.00  --trig_cnt_out_sk_spl                   false
% 1.67/1.00  --abstr_cl_out                          false
% 1.67/1.00  
% 1.67/1.00  ------ Global Options
% 1.67/1.00  
% 1.67/1.00  --schedule                              default
% 1.67/1.00  --add_important_lit                     false
% 1.67/1.00  --prop_solver_per_cl                    1000
% 1.67/1.00  --min_unsat_core                        false
% 1.67/1.00  --soft_assumptions                      false
% 1.67/1.00  --soft_lemma_size                       3
% 1.67/1.00  --prop_impl_unit_size                   0
% 1.67/1.00  --prop_impl_unit                        []
% 1.67/1.00  --share_sel_clauses                     true
% 1.67/1.00  --reset_solvers                         false
% 1.67/1.00  --bc_imp_inh                            [conj_cone]
% 1.67/1.00  --conj_cone_tolerance                   3.
% 1.67/1.00  --extra_neg_conj                        none
% 1.67/1.00  --large_theory_mode                     true
% 1.67/1.00  --prolific_symb_bound                   200
% 1.67/1.00  --lt_threshold                          2000
% 1.67/1.00  --clause_weak_htbl                      true
% 1.67/1.00  --gc_record_bc_elim                     false
% 1.67/1.00  
% 1.67/1.00  ------ Preprocessing Options
% 1.67/1.00  
% 1.67/1.00  --preprocessing_flag                    true
% 1.67/1.00  --time_out_prep_mult                    0.1
% 1.67/1.00  --splitting_mode                        input
% 1.67/1.00  --splitting_grd                         true
% 1.67/1.00  --splitting_cvd                         false
% 1.67/1.00  --splitting_cvd_svl                     false
% 1.67/1.00  --splitting_nvd                         32
% 1.67/1.00  --sub_typing                            true
% 1.67/1.00  --prep_gs_sim                           true
% 1.67/1.00  --prep_unflatten                        true
% 1.67/1.00  --prep_res_sim                          true
% 1.67/1.00  --prep_upred                            true
% 1.67/1.00  --prep_sem_filter                       exhaustive
% 1.67/1.00  --prep_sem_filter_out                   false
% 1.67/1.00  --pred_elim                             true
% 1.67/1.00  --res_sim_input                         true
% 1.67/1.00  --eq_ax_congr_red                       true
% 1.67/1.00  --pure_diseq_elim                       true
% 1.67/1.00  --brand_transform                       false
% 1.67/1.00  --non_eq_to_eq                          false
% 1.67/1.00  --prep_def_merge                        true
% 1.67/1.00  --prep_def_merge_prop_impl              false
% 1.67/1.00  --prep_def_merge_mbd                    true
% 1.67/1.00  --prep_def_merge_tr_red                 false
% 1.67/1.00  --prep_def_merge_tr_cl                  false
% 1.67/1.00  --smt_preprocessing                     true
% 1.67/1.00  --smt_ac_axioms                         fast
% 1.67/1.00  --preprocessed_out                      false
% 1.67/1.00  --preprocessed_stats                    false
% 1.67/1.00  
% 1.67/1.00  ------ Abstraction refinement Options
% 1.67/1.00  
% 1.67/1.00  --abstr_ref                             []
% 1.67/1.00  --abstr_ref_prep                        false
% 1.67/1.00  --abstr_ref_until_sat                   false
% 1.67/1.00  --abstr_ref_sig_restrict                funpre
% 1.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.67/1.00  --abstr_ref_under                       []
% 1.67/1.00  
% 1.67/1.00  ------ SAT Options
% 1.67/1.00  
% 1.67/1.00  --sat_mode                              false
% 1.67/1.00  --sat_fm_restart_options                ""
% 1.67/1.00  --sat_gr_def                            false
% 1.67/1.00  --sat_epr_types                         true
% 1.67/1.00  --sat_non_cyclic_types                  false
% 1.67/1.00  --sat_finite_models                     false
% 1.67/1.00  --sat_fm_lemmas                         false
% 1.67/1.00  --sat_fm_prep                           false
% 1.67/1.00  --sat_fm_uc_incr                        true
% 1.67/1.00  --sat_out_model                         small
% 1.67/1.00  --sat_out_clauses                       false
% 1.67/1.00  
% 1.67/1.00  ------ QBF Options
% 1.67/1.00  
% 1.67/1.00  --qbf_mode                              false
% 1.67/1.00  --qbf_elim_univ                         false
% 1.67/1.00  --qbf_dom_inst                          none
% 1.67/1.00  --qbf_dom_pre_inst                      false
% 1.67/1.00  --qbf_sk_in                             false
% 1.67/1.00  --qbf_pred_elim                         true
% 1.67/1.00  --qbf_split                             512
% 1.67/1.00  
% 1.67/1.00  ------ BMC1 Options
% 1.67/1.00  
% 1.67/1.00  --bmc1_incremental                      false
% 1.67/1.00  --bmc1_axioms                           reachable_all
% 1.67/1.00  --bmc1_min_bound                        0
% 1.67/1.00  --bmc1_max_bound                        -1
% 1.67/1.00  --bmc1_max_bound_default                -1
% 1.67/1.00  --bmc1_symbol_reachability              true
% 1.67/1.00  --bmc1_property_lemmas                  false
% 1.67/1.00  --bmc1_k_induction                      false
% 1.67/1.00  --bmc1_non_equiv_states                 false
% 1.67/1.00  --bmc1_deadlock                         false
% 1.67/1.00  --bmc1_ucm                              false
% 1.67/1.00  --bmc1_add_unsat_core                   none
% 1.67/1.00  --bmc1_unsat_core_children              false
% 1.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.67/1.00  --bmc1_out_stat                         full
% 1.67/1.00  --bmc1_ground_init                      false
% 1.67/1.00  --bmc1_pre_inst_next_state              false
% 1.67/1.00  --bmc1_pre_inst_state                   false
% 1.67/1.00  --bmc1_pre_inst_reach_state             false
% 1.67/1.00  --bmc1_out_unsat_core                   false
% 1.67/1.00  --bmc1_aig_witness_out                  false
% 1.67/1.00  --bmc1_verbose                          false
% 1.67/1.00  --bmc1_dump_clauses_tptp                false
% 1.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.67/1.00  --bmc1_dump_file                        -
% 1.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.67/1.00  --bmc1_ucm_extend_mode                  1
% 1.67/1.00  --bmc1_ucm_init_mode                    2
% 1.67/1.00  --bmc1_ucm_cone_mode                    none
% 1.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.67/1.00  --bmc1_ucm_relax_model                  4
% 1.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.67/1.00  --bmc1_ucm_layered_model                none
% 1.67/1.00  --bmc1_ucm_max_lemma_size               10
% 1.67/1.00  
% 1.67/1.00  ------ AIG Options
% 1.67/1.00  
% 1.67/1.00  --aig_mode                              false
% 1.67/1.00  
% 1.67/1.00  ------ Instantiation Options
% 1.67/1.00  
% 1.67/1.00  --instantiation_flag                    true
% 1.67/1.00  --inst_sos_flag                         false
% 1.67/1.00  --inst_sos_phase                        true
% 1.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.67/1.00  --inst_lit_sel_side                     num_symb
% 1.67/1.00  --inst_solver_per_active                1400
% 1.67/1.00  --inst_solver_calls_frac                1.
% 1.67/1.00  --inst_passive_queue_type               priority_queues
% 1.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.67/1.00  --inst_passive_queues_freq              [25;2]
% 1.67/1.00  --inst_dismatching                      true
% 1.67/1.00  --inst_eager_unprocessed_to_passive     true
% 1.67/1.00  --inst_prop_sim_given                   true
% 1.67/1.00  --inst_prop_sim_new                     false
% 1.67/1.00  --inst_subs_new                         false
% 1.67/1.00  --inst_eq_res_simp                      false
% 1.67/1.00  --inst_subs_given                       false
% 1.67/1.00  --inst_orphan_elimination               true
% 1.67/1.00  --inst_learning_loop_flag               true
% 1.67/1.00  --inst_learning_start                   3000
% 1.67/1.00  --inst_learning_factor                  2
% 1.67/1.00  --inst_start_prop_sim_after_learn       3
% 1.67/1.00  --inst_sel_renew                        solver
% 1.67/1.00  --inst_lit_activity_flag                true
% 1.67/1.00  --inst_restr_to_given                   false
% 1.67/1.00  --inst_activity_threshold               500
% 1.67/1.00  --inst_out_proof                        true
% 1.67/1.00  
% 1.67/1.00  ------ Resolution Options
% 1.67/1.00  
% 1.67/1.00  --resolution_flag                       true
% 1.67/1.00  --res_lit_sel                           adaptive
% 1.67/1.00  --res_lit_sel_side                      none
% 1.67/1.00  --res_ordering                          kbo
% 1.67/1.00  --res_to_prop_solver                    active
% 1.67/1.00  --res_prop_simpl_new                    false
% 1.67/1.00  --res_prop_simpl_given                  true
% 1.67/1.00  --res_passive_queue_type                priority_queues
% 1.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.67/1.00  --res_passive_queues_freq               [15;5]
% 1.67/1.00  --res_forward_subs                      full
% 1.67/1.00  --res_backward_subs                     full
% 1.67/1.00  --res_forward_subs_resolution           true
% 1.67/1.00  --res_backward_subs_resolution          true
% 1.67/1.00  --res_orphan_elimination                true
% 1.67/1.00  --res_time_limit                        2.
% 1.67/1.00  --res_out_proof                         true
% 1.67/1.00  
% 1.67/1.00  ------ Superposition Options
% 1.67/1.00  
% 1.67/1.00  --superposition_flag                    true
% 1.67/1.00  --sup_passive_queue_type                priority_queues
% 1.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.67/1.00  --demod_completeness_check              fast
% 1.67/1.00  --demod_use_ground                      true
% 1.67/1.00  --sup_to_prop_solver                    passive
% 1.67/1.00  --sup_prop_simpl_new                    true
% 1.67/1.00  --sup_prop_simpl_given                  true
% 1.67/1.00  --sup_fun_splitting                     false
% 1.67/1.00  --sup_smt_interval                      50000
% 1.67/1.00  
% 1.67/1.00  ------ Superposition Simplification Setup
% 1.67/1.00  
% 1.67/1.00  --sup_indices_passive                   []
% 1.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.00  --sup_full_bw                           [BwDemod]
% 1.67/1.00  --sup_immed_triv                        [TrivRules]
% 1.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.00  --sup_immed_bw_main                     []
% 1.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/1.00  
% 1.67/1.00  ------ Combination Options
% 1.67/1.00  
% 1.67/1.00  --comb_res_mult                         3
% 1.67/1.00  --comb_sup_mult                         2
% 1.67/1.00  --comb_inst_mult                        10
% 1.67/1.00  
% 1.67/1.00  ------ Debug Options
% 1.67/1.00  
% 1.67/1.00  --dbg_backtrace                         false
% 1.67/1.00  --dbg_dump_prop_clauses                 false
% 1.67/1.00  --dbg_dump_prop_clauses_file            -
% 1.67/1.00  --dbg_out_stat                          false
% 1.67/1.00  ------ Parsing...
% 1.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.67/1.00  
% 1.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.67/1.00  
% 1.67/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.67/1.00  
% 1.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.67/1.00  ------ Proving...
% 1.67/1.00  ------ Problem Properties 
% 1.67/1.00  
% 1.67/1.00  
% 1.67/1.00  clauses                                 12
% 1.67/1.00  conjectures                             2
% 1.67/1.00  EPR                                     1
% 1.67/1.00  Horn                                    11
% 1.67/1.00  unary                                   4
% 1.67/1.00  binary                                  4
% 1.67/1.00  lits                                    24
% 1.67/1.00  lits eq                                 6
% 1.67/1.00  fd_pure                                 0
% 1.67/1.00  fd_pseudo                               0
% 1.67/1.00  fd_cond                                 0
% 1.67/1.00  fd_pseudo_cond                          0
% 1.67/1.00  AC symbols                              0
% 1.67/1.00  
% 1.67/1.00  ------ Schedule dynamic 5 is on 
% 1.67/1.00  
% 1.67/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.67/1.00  
% 1.67/1.00  
% 1.67/1.00  ------ 
% 1.67/1.00  Current options:
% 1.67/1.00  ------ 
% 1.67/1.00  
% 1.67/1.00  ------ Input Options
% 1.67/1.00  
% 1.67/1.00  --out_options                           all
% 1.67/1.00  --tptp_safe_out                         true
% 1.67/1.00  --problem_path                          ""
% 1.67/1.00  --include_path                          ""
% 1.67/1.00  --clausifier                            res/vclausify_rel
% 1.67/1.00  --clausifier_options                    --mode clausify
% 1.67/1.00  --stdin                                 false
% 1.67/1.00  --stats_out                             all
% 1.67/1.00  
% 1.67/1.00  ------ General Options
% 1.67/1.00  
% 1.67/1.00  --fof                                   false
% 1.67/1.00  --time_out_real                         305.
% 1.67/1.00  --time_out_virtual                      -1.
% 1.67/1.00  --symbol_type_check                     false
% 1.67/1.00  --clausify_out                          false
% 1.67/1.00  --sig_cnt_out                           false
% 1.67/1.00  --trig_cnt_out                          false
% 1.67/1.00  --trig_cnt_out_tolerance                1.
% 1.67/1.00  --trig_cnt_out_sk_spl                   false
% 1.67/1.00  --abstr_cl_out                          false
% 1.67/1.00  
% 1.67/1.00  ------ Global Options
% 1.67/1.00  
% 1.67/1.00  --schedule                              default
% 1.67/1.00  --add_important_lit                     false
% 1.67/1.00  --prop_solver_per_cl                    1000
% 1.67/1.00  --min_unsat_core                        false
% 1.67/1.00  --soft_assumptions                      false
% 1.67/1.00  --soft_lemma_size                       3
% 1.67/1.00  --prop_impl_unit_size                   0
% 1.67/1.00  --prop_impl_unit                        []
% 1.67/1.00  --share_sel_clauses                     true
% 1.67/1.00  --reset_solvers                         false
% 1.67/1.00  --bc_imp_inh                            [conj_cone]
% 1.67/1.00  --conj_cone_tolerance                   3.
% 1.67/1.00  --extra_neg_conj                        none
% 1.67/1.00  --large_theory_mode                     true
% 1.67/1.00  --prolific_symb_bound                   200
% 1.67/1.00  --lt_threshold                          2000
% 1.67/1.00  --clause_weak_htbl                      true
% 1.67/1.00  --gc_record_bc_elim                     false
% 1.67/1.00  
% 1.67/1.00  ------ Preprocessing Options
% 1.67/1.00  
% 1.67/1.00  --preprocessing_flag                    true
% 1.67/1.00  --time_out_prep_mult                    0.1
% 1.67/1.00  --splitting_mode                        input
% 1.67/1.00  --splitting_grd                         true
% 1.67/1.00  --splitting_cvd                         false
% 1.67/1.00  --splitting_cvd_svl                     false
% 1.67/1.00  --splitting_nvd                         32
% 1.67/1.00  --sub_typing                            true
% 1.67/1.00  --prep_gs_sim                           true
% 1.67/1.00  --prep_unflatten                        true
% 1.67/1.00  --prep_res_sim                          true
% 1.67/1.00  --prep_upred                            true
% 1.67/1.00  --prep_sem_filter                       exhaustive
% 1.67/1.00  --prep_sem_filter_out                   false
% 1.67/1.00  --pred_elim                             true
% 1.67/1.00  --res_sim_input                         true
% 1.67/1.00  --eq_ax_congr_red                       true
% 1.67/1.00  --pure_diseq_elim                       true
% 1.67/1.00  --brand_transform                       false
% 1.67/1.00  --non_eq_to_eq                          false
% 1.67/1.00  --prep_def_merge                        true
% 1.67/1.00  --prep_def_merge_prop_impl              false
% 1.67/1.00  --prep_def_merge_mbd                    true
% 1.67/1.00  --prep_def_merge_tr_red                 false
% 1.67/1.00  --prep_def_merge_tr_cl                  false
% 1.67/1.00  --smt_preprocessing                     true
% 1.67/1.00  --smt_ac_axioms                         fast
% 1.67/1.00  --preprocessed_out                      false
% 1.67/1.00  --preprocessed_stats                    false
% 1.67/1.00  
% 1.67/1.00  ------ Abstraction refinement Options
% 1.67/1.00  
% 1.67/1.00  --abstr_ref                             []
% 1.67/1.00  --abstr_ref_prep                        false
% 1.67/1.00  --abstr_ref_until_sat                   false
% 1.67/1.00  --abstr_ref_sig_restrict                funpre
% 1.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.67/1.00  --abstr_ref_under                       []
% 1.67/1.00  
% 1.67/1.00  ------ SAT Options
% 1.67/1.00  
% 1.67/1.00  --sat_mode                              false
% 1.67/1.00  --sat_fm_restart_options                ""
% 1.67/1.00  --sat_gr_def                            false
% 1.67/1.00  --sat_epr_types                         true
% 1.67/1.00  --sat_non_cyclic_types                  false
% 1.67/1.00  --sat_finite_models                     false
% 1.67/1.00  --sat_fm_lemmas                         false
% 1.67/1.00  --sat_fm_prep                           false
% 1.67/1.00  --sat_fm_uc_incr                        true
% 1.67/1.00  --sat_out_model                         small
% 1.67/1.00  --sat_out_clauses                       false
% 1.67/1.00  
% 1.67/1.00  ------ QBF Options
% 1.67/1.00  
% 1.67/1.00  --qbf_mode                              false
% 1.67/1.00  --qbf_elim_univ                         false
% 1.67/1.00  --qbf_dom_inst                          none
% 1.67/1.00  --qbf_dom_pre_inst                      false
% 1.67/1.00  --qbf_sk_in                             false
% 1.67/1.00  --qbf_pred_elim                         true
% 1.67/1.00  --qbf_split                             512
% 1.67/1.00  
% 1.67/1.00  ------ BMC1 Options
% 1.67/1.00  
% 1.67/1.00  --bmc1_incremental                      false
% 1.67/1.00  --bmc1_axioms                           reachable_all
% 1.67/1.00  --bmc1_min_bound                        0
% 1.67/1.00  --bmc1_max_bound                        -1
% 1.67/1.00  --bmc1_max_bound_default                -1
% 1.67/1.00  --bmc1_symbol_reachability              true
% 1.67/1.00  --bmc1_property_lemmas                  false
% 1.67/1.00  --bmc1_k_induction                      false
% 1.67/1.00  --bmc1_non_equiv_states                 false
% 1.67/1.00  --bmc1_deadlock                         false
% 1.67/1.00  --bmc1_ucm                              false
% 1.67/1.00  --bmc1_add_unsat_core                   none
% 1.67/1.00  --bmc1_unsat_core_children              false
% 1.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.67/1.00  --bmc1_out_stat                         full
% 1.67/1.00  --bmc1_ground_init                      false
% 1.67/1.00  --bmc1_pre_inst_next_state              false
% 1.67/1.00  --bmc1_pre_inst_state                   false
% 1.67/1.00  --bmc1_pre_inst_reach_state             false
% 1.67/1.00  --bmc1_out_unsat_core                   false
% 1.67/1.00  --bmc1_aig_witness_out                  false
% 1.67/1.00  --bmc1_verbose                          false
% 1.67/1.00  --bmc1_dump_clauses_tptp                false
% 1.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.67/1.00  --bmc1_dump_file                        -
% 1.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.67/1.00  --bmc1_ucm_extend_mode                  1
% 1.67/1.00  --bmc1_ucm_init_mode                    2
% 1.67/1.00  --bmc1_ucm_cone_mode                    none
% 1.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.67/1.00  --bmc1_ucm_relax_model                  4
% 1.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.67/1.00  --bmc1_ucm_layered_model                none
% 1.67/1.00  --bmc1_ucm_max_lemma_size               10
% 1.67/1.00  
% 1.67/1.00  ------ AIG Options
% 1.67/1.00  
% 1.67/1.00  --aig_mode                              false
% 1.67/1.00  
% 1.67/1.00  ------ Instantiation Options
% 1.67/1.00  
% 1.67/1.00  --instantiation_flag                    true
% 1.67/1.00  --inst_sos_flag                         false
% 1.67/1.00  --inst_sos_phase                        true
% 1.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.67/1.00  --inst_lit_sel_side                     none
% 1.67/1.00  --inst_solver_per_active                1400
% 1.67/1.00  --inst_solver_calls_frac                1.
% 1.67/1.00  --inst_passive_queue_type               priority_queues
% 1.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.67/1.00  --inst_passive_queues_freq              [25;2]
% 1.67/1.00  --inst_dismatching                      true
% 1.67/1.00  --inst_eager_unprocessed_to_passive     true
% 1.67/1.00  --inst_prop_sim_given                   true
% 1.67/1.00  --inst_prop_sim_new                     false
% 1.67/1.00  --inst_subs_new                         false
% 1.67/1.00  --inst_eq_res_simp                      false
% 1.67/1.00  --inst_subs_given                       false
% 1.67/1.00  --inst_orphan_elimination               true
% 1.67/1.00  --inst_learning_loop_flag               true
% 1.67/1.00  --inst_learning_start                   3000
% 1.67/1.00  --inst_learning_factor                  2
% 1.67/1.00  --inst_start_prop_sim_after_learn       3
% 1.67/1.00  --inst_sel_renew                        solver
% 1.67/1.00  --inst_lit_activity_flag                true
% 1.67/1.00  --inst_restr_to_given                   false
% 1.67/1.00  --inst_activity_threshold               500
% 1.67/1.00  --inst_out_proof                        true
% 1.67/1.00  
% 1.67/1.00  ------ Resolution Options
% 1.67/1.00  
% 1.67/1.00  --resolution_flag                       false
% 1.67/1.00  --res_lit_sel                           adaptive
% 1.67/1.00  --res_lit_sel_side                      none
% 1.67/1.00  --res_ordering                          kbo
% 1.67/1.00  --res_to_prop_solver                    active
% 1.67/1.00  --res_prop_simpl_new                    false
% 1.67/1.00  --res_prop_simpl_given                  true
% 1.67/1.00  --res_passive_queue_type                priority_queues
% 1.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.67/1.00  --res_passive_queues_freq               [15;5]
% 1.67/1.00  --res_forward_subs                      full
% 1.67/1.00  --res_backward_subs                     full
% 1.67/1.00  --res_forward_subs_resolution           true
% 1.67/1.00  --res_backward_subs_resolution          true
% 1.67/1.00  --res_orphan_elimination                true
% 1.67/1.00  --res_time_limit                        2.
% 1.67/1.00  --res_out_proof                         true
% 1.67/1.00  
% 1.67/1.00  ------ Superposition Options
% 1.67/1.00  
% 1.67/1.00  --superposition_flag                    true
% 1.67/1.00  --sup_passive_queue_type                priority_queues
% 1.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.67/1.00  --demod_completeness_check              fast
% 1.67/1.00  --demod_use_ground                      true
% 1.67/1.00  --sup_to_prop_solver                    passive
% 1.67/1.00  --sup_prop_simpl_new                    true
% 1.67/1.00  --sup_prop_simpl_given                  true
% 1.67/1.00  --sup_fun_splitting                     false
% 1.67/1.00  --sup_smt_interval                      50000
% 1.67/1.00  
% 1.67/1.00  ------ Superposition Simplification Setup
% 1.67/1.00  
% 1.67/1.00  --sup_indices_passive                   []
% 1.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.00  --sup_full_bw                           [BwDemod]
% 1.67/1.00  --sup_immed_triv                        [TrivRules]
% 1.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.00  --sup_immed_bw_main                     []
% 1.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/1.00  
% 1.67/1.00  ------ Combination Options
% 1.67/1.00  
% 1.67/1.00  --comb_res_mult                         3
% 1.67/1.00  --comb_sup_mult                         2
% 1.67/1.00  --comb_inst_mult                        10
% 1.67/1.00  
% 1.67/1.00  ------ Debug Options
% 1.67/1.00  
% 1.67/1.00  --dbg_backtrace                         false
% 1.67/1.00  --dbg_dump_prop_clauses                 false
% 1.67/1.00  --dbg_dump_prop_clauses_file            -
% 1.67/1.00  --dbg_out_stat                          false
% 1.67/1.00  
% 1.67/1.00  
% 1.67/1.00  
% 1.67/1.00  
% 1.67/1.00  ------ Proving...
% 1.67/1.00  
% 1.67/1.00  
% 1.67/1.00  % SZS status Theorem for theBenchmark.p
% 1.67/1.00  
% 1.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.67/1.00  
% 1.67/1.00  fof(f6,axiom,(
% 1.67/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/1.00  
% 1.67/1.00  fof(f17,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(ennf_transformation,[],[f6])).
% 1.67/1.00  
% 1.67/1.00  fof(f24,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(nnf_transformation,[],[f17])).
% 1.67/1.00  
% 1.67/1.00  fof(f37,plain,(
% 1.67/1.00    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/1.00    inference(cnf_transformation,[],[f24])).
% 1.67/1.00  
% 1.67/1.00  fof(f8,conjecture,(
% 1.67/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 1.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/1.00  
% 1.67/1.00  fof(f9,negated_conjecture,(
% 1.67/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 1.67/1.00    inference(negated_conjecture,[],[f8])).
% 1.67/1.00  
% 1.67/1.00  fof(f20,plain,(
% 1.67/1.00    ? [X0] : (? [X1] : (((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.67/1.00    inference(ennf_transformation,[],[f9])).
% 1.67/1.00  
% 1.67/1.00  fof(f21,plain,(
% 1.67/1.00    ? [X0] : (? [X1] : ((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.67/1.00    inference(flattening,[],[f20])).
% 1.67/1.00  
% 1.67/1.00  fof(f25,plain,(
% 1.67/1.00    ? [X0] : (? [X1] : (((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.67/1.00    inference(nnf_transformation,[],[f21])).
% 1.67/1.00  
% 1.67/1.00  fof(f26,plain,(
% 1.67/1.00    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.67/1.00    inference(flattening,[],[f25])).
% 1.67/1.00  
% 1.67/1.00  fof(f28,plain,(
% 1.67/1.00    ( ! [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v6_tops_1(sK1,X0) | ~v5_tops_1(sK1,X0)) & (v6_tops_1(sK1,X0) | v5_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & v3_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.67/1.00    introduced(choice_axiom,[])).
% 1.67/1.00  
% 1.67/1.00  fof(f27,plain,(
% 1.67/1.00    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.67/1.00    introduced(choice_axiom,[])).
% 1.67/1.00  
% 1.67/1.00  fof(f29,plain,(
% 1.67/1.00    ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 1.67/1.00  
% 1.67/1.00  fof(f43,plain,(
% 1.67/1.00    v4_pre_topc(sK1,sK0)),
% 1.67/1.00    inference(cnf_transformation,[],[f29])).
% 1.67/1.00  
% 1.67/1.00  fof(f40,plain,(
% 1.67/1.00    l1_pre_topc(sK0)),
% 1.67/1.00    inference(cnf_transformation,[],[f29])).
% 1.67/1.00  
% 1.67/1.00  fof(f41,plain,(
% 1.67/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/1.00    inference(cnf_transformation,[],[f29])).
% 1.67/1.00  
% 1.67/1.00  fof(f1,axiom,(
% 1.67/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/1.00  
% 1.67/1.00  fof(f11,plain,(
% 1.67/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/1.00    inference(ennf_transformation,[],[f1])).
% 1.67/1.00  
% 1.67/1.00  fof(f30,plain,(
% 1.67/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.67/1.00    inference(cnf_transformation,[],[f11])).
% 1.67/1.00  
% 1.67/1.00  fof(f7,axiom,(
% 1.67/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 1.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/1.00  
% 1.67/1.00  fof(f18,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(ennf_transformation,[],[f7])).
% 1.67/1.00  
% 1.67/1.00  fof(f19,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(flattening,[],[f18])).
% 1.67/1.00  
% 1.67/1.00  fof(f39,plain,(
% 1.67/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/1.00    inference(cnf_transformation,[],[f19])).
% 1.67/1.00  
% 1.67/1.00  fof(f2,axiom,(
% 1.67/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/1.00  
% 1.67/1.00  fof(f12,plain,(
% 1.67/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/1.00    inference(ennf_transformation,[],[f2])).
% 1.67/1.00  
% 1.67/1.00  fof(f31,plain,(
% 1.67/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.67/1.00    inference(cnf_transformation,[],[f12])).
% 1.67/1.00  
% 1.67/1.00  fof(f38,plain,(
% 1.67/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/1.00    inference(cnf_transformation,[],[f24])).
% 1.67/1.00  
% 1.67/1.00  fof(f3,axiom,(
% 1.67/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/1.00  
% 1.67/1.00  fof(f10,plain,(
% 1.67/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 1.67/1.00    inference(pure_predicate_removal,[],[f3])).
% 1.67/1.00  
% 1.67/1.00  fof(f13,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(ennf_transformation,[],[f10])).
% 1.67/1.00  
% 1.67/1.00  fof(f14,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(flattening,[],[f13])).
% 1.67/1.00  
% 1.67/1.00  fof(f32,plain,(
% 1.67/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/1.00    inference(cnf_transformation,[],[f14])).
% 1.67/1.00  
% 1.67/1.00  fof(f42,plain,(
% 1.67/1.00    v3_pre_topc(sK1,sK0)),
% 1.67/1.00    inference(cnf_transformation,[],[f29])).
% 1.67/1.00  
% 1.67/1.00  fof(f4,axiom,(
% 1.67/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/1.00  
% 1.67/1.00  fof(f15,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(ennf_transformation,[],[f4])).
% 1.67/1.00  
% 1.67/1.00  fof(f22,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(nnf_transformation,[],[f15])).
% 1.67/1.00  
% 1.67/1.00  fof(f34,plain,(
% 1.67/1.00    ( ! [X0,X1] : (v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/1.00    inference(cnf_transformation,[],[f22])).
% 1.67/1.00  
% 1.67/1.00  fof(f5,axiom,(
% 1.67/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/1.00  
% 1.67/1.00  fof(f16,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(ennf_transformation,[],[f5])).
% 1.67/1.00  
% 1.67/1.00  fof(f23,plain,(
% 1.67/1.00    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.67/1.00    inference(nnf_transformation,[],[f16])).
% 1.67/1.00  
% 1.67/1.00  fof(f36,plain,(
% 1.67/1.00    ( ! [X0,X1] : (v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/1.00    inference(cnf_transformation,[],[f23])).
% 1.67/1.00  
% 1.67/1.00  fof(f45,plain,(
% 1.67/1.00    ~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)),
% 1.67/1.00    inference(cnf_transformation,[],[f29])).
% 1.67/1.00  
% 1.67/1.00  cnf(c_8,plain,
% 1.67/1.00      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.67/1.00      | ~ v4_pre_topc(X1,X0)
% 1.67/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/1.00      | ~ l1_pre_topc(X0) ),
% 1.67/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_12,negated_conjecture,
% 1.67/1.00      ( v4_pre_topc(sK1,sK0) ),
% 1.67/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_274,plain,
% 1.67/1.00      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.67/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/1.00      | ~ l1_pre_topc(X0)
% 1.67/1.00      | sK0 != X0
% 1.67/1.00      | sK1 != X1 ),
% 1.67/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_275,plain,
% 1.67/1.00      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.67/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.00      | ~ l1_pre_topc(sK0) ),
% 1.67/1.00      inference(unflattening,[status(thm)],[c_274]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_15,negated_conjecture,
% 1.67/1.00      ( l1_pre_topc(sK0) ),
% 1.67/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_14,negated_conjecture,
% 1.67/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.67/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_277,plain,
% 1.67/1.00      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 1.67/1.00      inference(global_propositional_subsumption,
% 1.67/1.00                [status(thm)],
% 1.67/1.00                [c_275,c_15,c_14]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_611,plain,
% 1.67/1.00      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 1.67/1.00      inference(subtyping,[status(esa)],[c_277]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_933,plain,
% 1.67/1.00      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
% 1.67/1.00      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_0,plain,
% 1.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.67/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 1.67/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_617,plain,
% 1.67/1.00      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 1.67/1.00      | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) ),
% 1.67/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_927,plain,
% 1.67/1.00      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
% 1.67/1.00      | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) = iProver_top ),
% 1.67/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_9,plain,
% 1.67/1.00      ( ~ v3_pre_topc(X0,X1)
% 1.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/1.00      | ~ l1_pre_topc(X1)
% 1.67/1.00      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0) ),
% 1.67/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_316,plain,
% 1.67/1.00      ( ~ v3_pre_topc(X0,X1)
% 1.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/1.00      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0)
% 1.67/1.00      | sK0 != X1 ),
% 1.67/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_317,plain,
% 1.67/1.00      ( ~ v3_pre_topc(X0,sK0)
% 1.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0) ),
% 1.67/1.00      inference(unflattening,[status(thm)],[c_316]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_608,plain,
% 1.67/1.00      ( ~ v3_pre_topc(X0_41,sK0)
% 1.67/1.00      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0_41))) = k2_pre_topc(sK0,X0_41) ),
% 1.67/1.00      inference(subtyping,[status(esa)],[c_317]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_935,plain,
% 1.67/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0_41))) = k2_pre_topc(sK0,X0_41)
% 1.67/1.00      | v3_pre_topc(X0_41,sK0) != iProver_top
% 1.67/1.00      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.67/1.00      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_1336,plain,
% 1.67/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_41)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_41))
% 1.67/1.00      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0_41),sK0) != iProver_top
% 1.67/1.00      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.67/1.00      inference(superposition,[status(thm)],[c_927,c_935]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_1666,plain,
% 1.67/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 1.67/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.67/1.00      inference(superposition,[status(thm)],[c_933,c_1336]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_614,negated_conjecture,
% 1.67/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.67/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_930,plain,
% 1.67/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.67/1.00      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_1,plain,
% 1.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.67/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 1.67/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_616,plain,
% 1.67/1.00      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 1.67/1.00      | k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41 ),
% 1.67/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_928,plain,
% 1.67/1.00      ( k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41
% 1.67/1.00      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 1.67/1.00      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_1162,plain,
% 1.67/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 1.67/1.00      inference(superposition,[status(thm)],[c_930,c_928]) ).
% 1.67/1.00  
% 1.67/1.00  cnf(c_7,plain,
% 1.67/1.01      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.67/1.01      | v4_pre_topc(X1,X0)
% 1.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/1.01      | ~ l1_pre_topc(X0) ),
% 1.67/1.01      inference(cnf_transformation,[],[f38]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_2,plain,
% 1.67/1.01      ( ~ v4_pre_topc(X0,X1)
% 1.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/1.01      | ~ l1_pre_topc(X1)
% 1.67/1.01      | k2_pre_topc(X1,X0) = X0 ),
% 1.67/1.01      inference(cnf_transformation,[],[f32]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_256,plain,
% 1.67/1.01      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.67/1.01      | ~ l1_pre_topc(X0)
% 1.67/1.01      | ~ l1_pre_topc(X3)
% 1.67/1.01      | X2 != X1
% 1.67/1.01      | X3 != X0
% 1.67/1.01      | k2_pre_topc(X3,X2) = X2 ),
% 1.67/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_2]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_257,plain,
% 1.67/1.01      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/1.01      | ~ l1_pre_topc(X0)
% 1.67/1.01      | k2_pre_topc(X0,X1) = X1 ),
% 1.67/1.01      inference(unflattening,[status(thm)],[c_256]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_301,plain,
% 1.67/1.01      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/1.01      | k2_pre_topc(X0,X1) = X1
% 1.67/1.01      | sK0 != X0 ),
% 1.67/1.01      inference(resolution_lifted,[status(thm)],[c_257,c_15]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_302,plain,
% 1.67/1.01      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 1.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | k2_pre_topc(sK0,X0) = X0 ),
% 1.67/1.01      inference(unflattening,[status(thm)],[c_301]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_609,plain,
% 1.67/1.01      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0_41),sK0)
% 1.67/1.01      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | k2_pre_topc(sK0,X0_41) = X0_41 ),
% 1.67/1.01      inference(subtyping,[status(esa)],[c_302]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_934,plain,
% 1.67/1.01      ( k2_pre_topc(sK0,X0_41) = X0_41
% 1.67/1.01      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0_41),sK0) != iProver_top
% 1.67/1.01      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.67/1.01      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_1242,plain,
% 1.67/1.01      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1)
% 1.67/1.01      | v3_pre_topc(sK1,sK0) != iProver_top
% 1.67/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.67/1.01      inference(superposition,[status(thm)],[c_1162,c_934]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_17,plain,
% 1.67/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.67/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_13,negated_conjecture,
% 1.67/1.01      ( v3_pre_topc(sK1,sK0) ),
% 1.67/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_18,plain,
% 1.67/1.01      ( v3_pre_topc(sK1,sK0) = iProver_top ),
% 1.67/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_1022,plain,
% 1.67/1.01      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.67/1.01      inference(instantiation,[status(thm)],[c_617]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_1023,plain,
% 1.67/1.01      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.67/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_1524,plain,
% 1.67/1.01      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 1.67/1.01      inference(global_propositional_subsumption,
% 1.67/1.01                [status(thm)],
% 1.67/1.01                [c_1242,c_17,c_18,c_1023]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_1674,plain,
% 1.67/1.01      ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
% 1.67/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.67/1.01      inference(light_normalisation,[status(thm)],[c_1666,c_1524]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_1335,plain,
% 1.67/1.01      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 1.67/1.01      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 1.67/1.01      inference(superposition,[status(thm)],[c_930,c_935]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_285,plain,
% 1.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/1.01      | ~ l1_pre_topc(X1)
% 1.67/1.01      | k2_pre_topc(X1,X0) = X0
% 1.67/1.01      | sK0 != X1
% 1.67/1.01      | sK1 != X0 ),
% 1.67/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_286,plain,
% 1.67/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | ~ l1_pre_topc(sK0)
% 1.67/1.01      | k2_pre_topc(sK0,sK1) = sK1 ),
% 1.67/1.01      inference(unflattening,[status(thm)],[c_285]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_288,plain,
% 1.67/1.01      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 1.67/1.01      inference(global_propositional_subsumption,
% 1.67/1.01                [status(thm)],
% 1.67/1.01                [c_286,c_15,c_14]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_610,plain,
% 1.67/1.01      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 1.67/1.01      inference(subtyping,[status(esa)],[c_288]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_1345,plain,
% 1.67/1.01      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
% 1.67/1.01      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 1.67/1.01      inference(light_normalisation,[status(thm)],[c_1335,c_610]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_3,plain,
% 1.67/1.01      ( v5_tops_1(X0,X1)
% 1.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/1.01      | ~ l1_pre_topc(X1)
% 1.67/1.01      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
% 1.67/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_346,plain,
% 1.67/1.01      ( v5_tops_1(X0,X1)
% 1.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/1.01      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 1.67/1.01      | sK0 != X1 ),
% 1.67/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_347,plain,
% 1.67/1.01      ( v5_tops_1(X0,sK0)
% 1.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
% 1.67/1.01      inference(unflattening,[status(thm)],[c_346]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_606,plain,
% 1.67/1.01      ( v5_tops_1(X0_41,sK0)
% 1.67/1.01      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | k2_pre_topc(sK0,k1_tops_1(sK0,X0_41)) != X0_41 ),
% 1.67/1.01      inference(subtyping,[status(esa)],[c_347]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_1071,plain,
% 1.67/1.01      ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.67/1.01      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 1.67/1.01      inference(instantiation,[status(thm)],[c_606]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_654,plain,
% 1.67/1.01      ( v5_tops_1(sK1,sK0)
% 1.67/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != sK1 ),
% 1.67/1.01      inference(instantiation,[status(thm)],[c_606]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_5,plain,
% 1.67/1.01      ( v6_tops_1(X0,X1)
% 1.67/1.01      | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 1.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/1.01      | ~ l1_pre_topc(X1) ),
% 1.67/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_10,negated_conjecture,
% 1.67/1.01      ( ~ v6_tops_1(sK1,sK0) | ~ v5_tops_1(sK1,sK0) ),
% 1.67/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_120,plain,
% 1.67/1.01      ( ~ v6_tops_1(sK1,sK0) | ~ v5_tops_1(sK1,sK0) ),
% 1.67/1.01      inference(prop_impl,[status(thm)],[c_10]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_221,plain,
% 1.67/1.01      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.67/1.01      | ~ v5_tops_1(sK1,sK0)
% 1.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/1.01      | ~ l1_pre_topc(X0)
% 1.67/1.01      | sK0 != X0
% 1.67/1.01      | sK1 != X1 ),
% 1.67/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_120]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_222,plain,
% 1.67/1.01      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.67/1.01      | ~ v5_tops_1(sK1,sK0)
% 1.67/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.67/1.01      | ~ l1_pre_topc(sK0) ),
% 1.67/1.01      inference(unflattening,[status(thm)],[c_221]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(c_224,plain,
% 1.67/1.01      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.67/1.01      | ~ v5_tops_1(sK1,sK0) ),
% 1.67/1.01      inference(global_propositional_subsumption,
% 1.67/1.01                [status(thm)],
% 1.67/1.01                [c_222,c_15,c_14]) ).
% 1.67/1.01  
% 1.67/1.01  cnf(contradiction,plain,
% 1.67/1.01      ( $false ),
% 1.67/1.01      inference(minisat,
% 1.67/1.01                [status(thm)],
% 1.67/1.01                [c_1674,c_1345,c_1071,c_1022,c_654,c_224,c_18,c_17,c_14]) ).
% 1.67/1.01  
% 1.67/1.01  
% 1.67/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.67/1.01  
% 1.67/1.01  ------                               Statistics
% 1.67/1.01  
% 1.67/1.01  ------ General
% 1.67/1.01  
% 1.67/1.01  abstr_ref_over_cycles:                  0
% 1.67/1.01  abstr_ref_under_cycles:                 0
% 1.67/1.01  gc_basic_clause_elim:                   0
% 1.67/1.01  forced_gc_time:                         0
% 1.67/1.01  parsing_time:                           0.018
% 1.67/1.01  unif_index_cands_time:                  0.
% 1.67/1.01  unif_index_add_time:                    0.
% 1.67/1.01  orderings_time:                         0.
% 1.67/1.01  out_proof_time:                         0.013
% 1.67/1.01  total_time:                             0.091
% 1.67/1.01  num_of_symbols:                         45
% 1.67/1.01  num_of_terms:                           1062
% 1.67/1.01  
% 1.67/1.01  ------ Preprocessing
% 1.67/1.01  
% 1.67/1.01  num_of_splits:                          0
% 1.67/1.01  num_of_split_atoms:                     0
% 1.67/1.01  num_of_reused_defs:                     0
% 1.67/1.01  num_eq_ax_congr_red:                    10
% 1.67/1.01  num_of_sem_filtered_clauses:            1
% 1.67/1.01  num_of_subtypes:                        4
% 1.67/1.01  monotx_restored_types:                  0
% 1.67/1.01  sat_num_of_epr_types:                   0
% 1.67/1.01  sat_num_of_non_cyclic_types:            0
% 1.67/1.01  sat_guarded_non_collapsed_types:        1
% 1.67/1.01  num_pure_diseq_elim:                    0
% 1.67/1.01  simp_replaced_by:                       0
% 1.67/1.01  res_preprocessed:                       69
% 1.67/1.01  prep_upred:                             0
% 1.67/1.01  prep_unflattend:                        18
% 1.67/1.01  smt_new_axioms:                         0
% 1.67/1.01  pred_elim_cands:                        3
% 1.67/1.01  pred_elim:                              3
% 1.67/1.01  pred_elim_cl:                           4
% 1.67/1.01  pred_elim_cycles:                       5
% 1.67/1.01  merged_defs:                            8
% 1.67/1.01  merged_defs_ncl:                        0
% 1.67/1.01  bin_hyper_res:                          8
% 1.67/1.01  prep_cycles:                            4
% 1.67/1.01  pred_elim_time:                         0.004
% 1.67/1.01  splitting_time:                         0.
% 1.67/1.01  sem_filter_time:                        0.
% 1.67/1.01  monotx_time:                            0.
% 1.67/1.01  subtype_inf_time:                       0.
% 1.67/1.01  
% 1.67/1.01  ------ Problem properties
% 1.67/1.01  
% 1.67/1.01  clauses:                                12
% 1.67/1.01  conjectures:                            2
% 1.67/1.01  epr:                                    1
% 1.67/1.01  horn:                                   11
% 1.67/1.01  ground:                                 6
% 1.67/1.01  unary:                                  4
% 1.67/1.01  binary:                                 4
% 1.67/1.01  lits:                                   24
% 1.67/1.01  lits_eq:                                6
% 1.67/1.01  fd_pure:                                0
% 1.67/1.01  fd_pseudo:                              0
% 1.67/1.01  fd_cond:                                0
% 1.67/1.01  fd_pseudo_cond:                         0
% 1.67/1.01  ac_symbols:                             0
% 1.67/1.01  
% 1.67/1.01  ------ Propositional Solver
% 1.67/1.01  
% 1.67/1.01  prop_solver_calls:                      26
% 1.67/1.01  prop_fast_solver_calls:                 415
% 1.67/1.01  smt_solver_calls:                       0
% 1.67/1.01  smt_fast_solver_calls:                  0
% 1.67/1.01  prop_num_of_clauses:                    394
% 1.67/1.01  prop_preprocess_simplified:             2119
% 1.67/1.01  prop_fo_subsumed:                       14
% 1.67/1.01  prop_solver_time:                       0.
% 1.67/1.01  smt_solver_time:                        0.
% 1.67/1.01  smt_fast_solver_time:                   0.
% 1.67/1.01  prop_fast_solver_time:                  0.
% 1.67/1.01  prop_unsat_core_time:                   0.
% 1.67/1.01  
% 1.67/1.01  ------ QBF
% 1.67/1.01  
% 1.67/1.01  qbf_q_res:                              0
% 1.67/1.01  qbf_num_tautologies:                    0
% 1.67/1.01  qbf_prep_cycles:                        0
% 1.67/1.01  
% 1.67/1.01  ------ BMC1
% 1.67/1.01  
% 1.67/1.01  bmc1_current_bound:                     -1
% 1.67/1.01  bmc1_last_solved_bound:                 -1
% 1.67/1.01  bmc1_unsat_core_size:                   -1
% 1.67/1.01  bmc1_unsat_core_parents_size:           -1
% 1.67/1.01  bmc1_merge_next_fun:                    0
% 1.67/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.67/1.01  
% 1.67/1.01  ------ Instantiation
% 1.67/1.01  
% 1.67/1.01  inst_num_of_clauses:                    163
% 1.67/1.01  inst_num_in_passive:                    3
% 1.67/1.01  inst_num_in_active:                     89
% 1.67/1.01  inst_num_in_unprocessed:                71
% 1.67/1.01  inst_num_of_loops:                      100
% 1.67/1.01  inst_num_of_learning_restarts:          0
% 1.67/1.01  inst_num_moves_active_passive:          6
% 1.67/1.01  inst_lit_activity:                      0
% 1.67/1.01  inst_lit_activity_moves:                0
% 1.67/1.01  inst_num_tautologies:                   0
% 1.67/1.01  inst_num_prop_implied:                  0
% 1.67/1.01  inst_num_existing_simplified:           0
% 1.67/1.01  inst_num_eq_res_simplified:             0
% 1.67/1.01  inst_num_child_elim:                    0
% 1.67/1.01  inst_num_of_dismatching_blockings:      57
% 1.67/1.01  inst_num_of_non_proper_insts:           187
% 1.67/1.01  inst_num_of_duplicates:                 0
% 1.67/1.01  inst_inst_num_from_inst_to_res:         0
% 1.67/1.01  inst_dismatching_checking_time:         0.
% 1.67/1.01  
% 1.67/1.01  ------ Resolution
% 1.67/1.01  
% 1.67/1.01  res_num_of_clauses:                     0
% 1.67/1.01  res_num_in_passive:                     0
% 1.67/1.01  res_num_in_active:                      0
% 1.67/1.01  res_num_of_loops:                       73
% 1.67/1.01  res_forward_subset_subsumed:            15
% 1.67/1.01  res_backward_subset_subsumed:           0
% 1.67/1.01  res_forward_subsumed:                   0
% 1.67/1.01  res_backward_subsumed:                  0
% 1.67/1.01  res_forward_subsumption_resolution:     0
% 1.67/1.01  res_backward_subsumption_resolution:    0
% 1.67/1.01  res_clause_to_clause_subsumption:       33
% 1.67/1.01  res_orphan_elimination:                 0
% 1.67/1.01  res_tautology_del:                      45
% 1.67/1.01  res_num_eq_res_simplified:              0
% 1.67/1.01  res_num_sel_changes:                    0
% 1.67/1.01  res_moves_from_active_to_pass:          0
% 1.67/1.01  
% 1.67/1.01  ------ Superposition
% 1.67/1.01  
% 1.67/1.01  sup_time_total:                         0.
% 1.67/1.01  sup_time_generating:                    0.
% 1.67/1.01  sup_time_sim_full:                      0.
% 1.67/1.01  sup_time_sim_immed:                     0.
% 1.67/1.01  
% 1.67/1.01  sup_num_of_clauses:                     21
% 1.67/1.01  sup_num_in_active:                      18
% 1.67/1.01  sup_num_in_passive:                     3
% 1.67/1.01  sup_num_of_loops:                       18
% 1.67/1.01  sup_fw_superposition:                   11
% 1.67/1.01  sup_bw_superposition:                   4
% 1.67/1.01  sup_immediate_simplified:               7
% 1.67/1.01  sup_given_eliminated:                   0
% 1.67/1.01  comparisons_done:                       0
% 1.67/1.01  comparisons_avoided:                    0
% 1.67/1.01  
% 1.67/1.01  ------ Simplifications
% 1.67/1.01  
% 1.67/1.01  
% 1.67/1.01  sim_fw_subset_subsumed:                 3
% 1.67/1.01  sim_bw_subset_subsumed:                 1
% 1.67/1.01  sim_fw_subsumed:                        0
% 1.67/1.01  sim_bw_subsumed:                        0
% 1.67/1.01  sim_fw_subsumption_res:                 0
% 1.67/1.01  sim_bw_subsumption_res:                 0
% 1.67/1.01  sim_tautology_del:                      0
% 1.67/1.01  sim_eq_tautology_del:                   2
% 1.67/1.01  sim_eq_res_simp:                        0
% 1.67/1.01  sim_fw_demodulated:                     0
% 1.67/1.01  sim_bw_demodulated:                     0
% 1.67/1.01  sim_light_normalised:                   4
% 1.67/1.01  sim_joinable_taut:                      0
% 1.67/1.01  sim_joinable_simp:                      0
% 1.67/1.01  sim_ac_normalised:                      0
% 1.67/1.01  sim_smt_subsumption:                    0
% 1.67/1.01  
%------------------------------------------------------------------------------
