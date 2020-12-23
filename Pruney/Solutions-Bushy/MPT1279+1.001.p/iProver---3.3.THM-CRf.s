%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1279+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:19 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  122 (1621 expanded)
%              Number of clauses        :   83 ( 592 expanded)
%              Number of leaves         :   10 ( 330 expanded)
%              Depth                    :   24
%              Number of atoms          :  346 (6172 expanded)
%              Number of equality atoms :  141 ( 736 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
            <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v6_tops_1(X1,X0)
          <~> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v6_tops_1(X1,X0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v6_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v6_tops_1(X1,X0) )
          & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v6_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f26,plain,
    ( ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v6_tops_1(sK1,sK0) )
    & ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v6_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f38,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,negated_conjecture,
    ( v6_tops_1(sK1,sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_155,negated_conjecture,
    ( v6_tops_1(sK1,sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_505,plain,
    ( v6_tops_1(sK1,sK0) = iProver_top
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
    | m1_subset_1(k3_subset_1(X0_42,X0_40),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_502,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_42,X0_40),k1_zfmisc_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_2,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_163,plain,
    ( ~ v5_tops_1(X0_40,X0_39)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) = X0_40 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_497,plain,
    ( k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) = X0_40
    | v5_tops_1(X0_40,X0_39) != iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_1065,plain,
    ( k2_pre_topc(X0_39,k1_tops_1(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k3_subset_1(u1_struct_0(X0_39),X0_40)
    | v5_tops_1(k3_subset_1(u1_struct_0(X0_39),X0_40),X0_39) != iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_497])).

cnf(c_6342,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | v6_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_1065])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_154,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_506,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_165,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k1_tops_1(X0_39,X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_495,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))) = k1_tops_1(X0_39,X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_879,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),X0_40)))) = k1_tops_1(X0_39,k3_subset_1(u1_struct_0(X0_39),X0_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_495])).

cnf(c_2535,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_506,c_879])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_157,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
    | k3_subset_1(X0_42,k3_subset_1(X0_42,X0_40)) = X0_40 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_503,plain,
    ( k3_subset_1(X0_42,k3_subset_1(X0_42,X0_40)) = X0_40
    | m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_803,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_506,c_503])).

cnf(c_2577,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2535,c_803])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3208,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2577,c_13])).

cnf(c_3212,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3208,c_502])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_621,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_622,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | m1_subset_1(k1_tops_1(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_1463,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_3580,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3212,c_13,c_14,c_622,c_1463])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_501,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39))) = iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_996,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,X0_40))) = k2_pre_topc(X0_39,X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_501,c_503])).

cnf(c_3589,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_996])).

cnf(c_627,plain,
    ( ~ m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39)))
    | k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k2_pre_topc(X0_39,X0_40))) = k2_pre_topc(X0_39,X0_40) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_1488,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_2272,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_6158,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3589,c_12,c_11,c_621,c_1462,c_1488,c_2272])).

cnf(c_2963,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_506,c_996])).

cnf(c_202,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_634,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_3202,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2963,c_12,c_11,c_202,c_634])).

cnf(c_3205,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3202,c_502])).

cnf(c_201,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39))) = iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_203,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_3307,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3205,c_13,c_14,c_203])).

cnf(c_3321,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3307,c_495])).

cnf(c_3324,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3321,c_3208])).

cnf(c_4709,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3324,c_13])).

cnf(c_6160,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_6158,c_4709])).

cnf(c_6509,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | v6_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6342,c_6160])).

cnf(c_7194,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | v6_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6509,c_13,c_14])).

cnf(c_4,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_161,plain,
    ( ~ v6_tops_1(X0_40,X0_39)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) = X0_40 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_499,plain,
    ( k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) = X0_40
    | v6_tops_1(X0_40,X0_39) != iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_1682,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | v6_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_506,c_499])).

cnf(c_1962,plain,
    ( v6_tops_1(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1682,c_13])).

cnf(c_1963,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1
    | v6_tops_1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1962])).

cnf(c_7200,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),sK1)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_7194,c_1963])).

cnf(c_500,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | m1_subset_1(k1_tops_1(X0_39,X0_40),k1_zfmisc_1(u1_struct_0(X0_39))) = iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_972,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k1_tops_1(X0_39,X0_40))) = k1_tops_1(X0_39,X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_503])).

cnf(c_3317,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3307,c_972])).

cnf(c_2924,plain,
    ( k3_subset_1(u1_struct_0(X0_39),k3_subset_1(u1_struct_0(X0_39),k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)))) = k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39))) != iProver_top
    | l1_pre_topc(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_501,c_972])).

cnf(c_2955,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2924])).

cnf(c_4526,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3317,c_13,c_14,c_2955])).

cnf(c_7207,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_7200,c_4526])).

cnf(c_7210,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_7207,c_803])).

cnf(c_7350,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_7210,c_6160])).

cnf(c_1,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_164,plain,
    ( v5_tops_1(X0_40,X0_39)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k2_pre_topc(X0_39,k1_tops_1(X0_39,X0_40)) != X0_40 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_743,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_3,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_162,plain,
    ( v6_tops_1(X0_40,X0_39)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_39)))
    | ~ l1_pre_topc(X0_39)
    | k1_tops_1(X0_39,k2_pre_topc(X0_39,X0_40)) != X0_40 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_193,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_9,negated_conjecture,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7350,c_7210,c_743,c_621,c_193,c_9,c_11,c_12])).


%------------------------------------------------------------------------------
