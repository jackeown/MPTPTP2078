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
% DateTime   : Thu Dec  3 12:15:38 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 249 expanded)
%              Number of clauses        :   49 (  83 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  197 ( 850 expanded)
%              Number of equality atoms :   86 ( 258 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_tops_1(X0,sK1) != k2_tops_1(X0,k1_tops_1(X0,sK1))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,X1) != k2_tops_1(sK0,k1_tops_1(sK0,X1))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20,f19])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_225,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_344,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_140,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_140])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_141])).

cnf(c_347,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_39),k1_tops_1(sK0,X0_39)) = k2_tops_1(sK0,X0_39) ),
    inference(subtyping,[status(esa)],[c_129])).

cnf(c_346,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_39),k1_tops_1(sK0,X0_39)) = k2_tops_1(sK0,X0_39)
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_559,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,X0_39)),k1_tops_1(sK0,k1_tops_1(sK0,X0_39))) = k2_tops_1(sK0,k1_tops_1(sK0,X0_39))
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_347,c_346])).

cnf(c_890,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_344,c_559])).

cnf(c_2,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_107,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_108,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_107])).

cnf(c_110,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_108,c_9,c_8])).

cnf(c_224,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_110])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_116,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_117,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_116])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0_39)) = k1_tops_1(sK0,X0_39) ),
    inference(subtyping,[status(esa)],[c_117])).

cnf(c_345,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0_39)) = k1_tops_1(sK0,X0_39)
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_408,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_344,c_345])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_152,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_153,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0_39)) = k2_pre_topc(sK0,X0_39) ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_348,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0_39)) = k2_pre_topc(sK0,X0_39)
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_497,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_39))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_39))
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_347,c_348])).

cnf(c_633,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_344,c_497])).

cnf(c_640,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_633,c_224])).

cnf(c_558,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_344,c_346])).

cnf(c_712,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_640,c_558])).

cnf(c_897,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_890,c_224,c_408,c_712])).

cnf(c_231,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_384,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != X0_43
    | k2_tops_1(sK0,sK1) != X0_43
    | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_395,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_6,negated_conjecture,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_226,negated_conjecture,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_228,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_243,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_235,plain,
    ( k2_tops_1(X0_42,X0_39) = k2_tops_1(X0_42,X1_39)
    | X0_39 != X1_39 ),
    theory(equality)).

cnf(c_240,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_897,c_395,c_226,c_243,c_240])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:44:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.43/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.43/1.05  
% 0.43/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.43/1.05  
% 0.43/1.05  ------  iProver source info
% 0.43/1.05  
% 0.43/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.43/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.43/1.05  git: non_committed_changes: false
% 0.43/1.05  git: last_make_outside_of_git: false
% 0.43/1.05  
% 0.43/1.05  ------ 
% 0.43/1.05  
% 0.43/1.05  ------ Input Options
% 0.43/1.05  
% 0.43/1.05  --out_options                           all
% 0.43/1.05  --tptp_safe_out                         true
% 0.43/1.05  --problem_path                          ""
% 0.43/1.05  --include_path                          ""
% 0.43/1.05  --clausifier                            res/vclausify_rel
% 0.43/1.05  --clausifier_options                    --mode clausify
% 0.43/1.05  --stdin                                 false
% 0.43/1.05  --stats_out                             all
% 0.43/1.05  
% 0.43/1.05  ------ General Options
% 0.43/1.05  
% 0.43/1.05  --fof                                   false
% 0.43/1.05  --time_out_real                         305.
% 0.43/1.05  --time_out_virtual                      -1.
% 0.43/1.05  --symbol_type_check                     false
% 0.43/1.05  --clausify_out                          false
% 0.43/1.05  --sig_cnt_out                           false
% 0.43/1.05  --trig_cnt_out                          false
% 0.43/1.05  --trig_cnt_out_tolerance                1.
% 0.43/1.05  --trig_cnt_out_sk_spl                   false
% 0.43/1.05  --abstr_cl_out                          false
% 0.43/1.05  
% 0.43/1.05  ------ Global Options
% 0.43/1.05  
% 0.43/1.05  --schedule                              default
% 0.43/1.05  --add_important_lit                     false
% 0.43/1.05  --prop_solver_per_cl                    1000
% 0.43/1.05  --min_unsat_core                        false
% 0.43/1.05  --soft_assumptions                      false
% 0.43/1.05  --soft_lemma_size                       3
% 0.43/1.05  --prop_impl_unit_size                   0
% 0.43/1.05  --prop_impl_unit                        []
% 0.43/1.05  --share_sel_clauses                     true
% 0.43/1.05  --reset_solvers                         false
% 0.43/1.05  --bc_imp_inh                            [conj_cone]
% 0.43/1.05  --conj_cone_tolerance                   3.
% 0.43/1.05  --extra_neg_conj                        none
% 0.43/1.05  --large_theory_mode                     true
% 0.43/1.05  --prolific_symb_bound                   200
% 0.43/1.05  --lt_threshold                          2000
% 0.43/1.05  --clause_weak_htbl                      true
% 0.43/1.05  --gc_record_bc_elim                     false
% 0.43/1.05  
% 0.43/1.05  ------ Preprocessing Options
% 0.43/1.05  
% 0.43/1.05  --preprocessing_flag                    true
% 0.43/1.05  --time_out_prep_mult                    0.1
% 0.43/1.05  --splitting_mode                        input
% 0.43/1.05  --splitting_grd                         true
% 0.43/1.05  --splitting_cvd                         false
% 0.43/1.05  --splitting_cvd_svl                     false
% 0.43/1.05  --splitting_nvd                         32
% 0.43/1.05  --sub_typing                            true
% 0.43/1.05  --prep_gs_sim                           true
% 0.43/1.05  --prep_unflatten                        true
% 0.43/1.05  --prep_res_sim                          true
% 0.43/1.05  --prep_upred                            true
% 0.43/1.05  --prep_sem_filter                       exhaustive
% 0.43/1.05  --prep_sem_filter_out                   false
% 0.43/1.05  --pred_elim                             true
% 0.43/1.05  --res_sim_input                         true
% 0.43/1.05  --eq_ax_congr_red                       true
% 0.43/1.05  --pure_diseq_elim                       true
% 0.43/1.05  --brand_transform                       false
% 0.43/1.05  --non_eq_to_eq                          false
% 0.43/1.05  --prep_def_merge                        true
% 0.43/1.05  --prep_def_merge_prop_impl              false
% 0.43/1.05  --prep_def_merge_mbd                    true
% 0.43/1.05  --prep_def_merge_tr_red                 false
% 0.43/1.05  --prep_def_merge_tr_cl                  false
% 0.43/1.05  --smt_preprocessing                     true
% 0.43/1.05  --smt_ac_axioms                         fast
% 0.43/1.05  --preprocessed_out                      false
% 0.43/1.05  --preprocessed_stats                    false
% 0.43/1.05  
% 0.43/1.05  ------ Abstraction refinement Options
% 0.43/1.05  
% 0.43/1.05  --abstr_ref                             []
% 0.43/1.05  --abstr_ref_prep                        false
% 0.43/1.05  --abstr_ref_until_sat                   false
% 0.43/1.05  --abstr_ref_sig_restrict                funpre
% 0.43/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.43/1.05  --abstr_ref_under                       []
% 0.43/1.05  
% 0.43/1.05  ------ SAT Options
% 0.43/1.05  
% 0.43/1.05  --sat_mode                              false
% 0.43/1.05  --sat_fm_restart_options                ""
% 0.43/1.05  --sat_gr_def                            false
% 0.43/1.05  --sat_epr_types                         true
% 0.43/1.05  --sat_non_cyclic_types                  false
% 0.43/1.05  --sat_finite_models                     false
% 0.43/1.05  --sat_fm_lemmas                         false
% 0.43/1.05  --sat_fm_prep                           false
% 0.43/1.05  --sat_fm_uc_incr                        true
% 0.43/1.05  --sat_out_model                         small
% 0.43/1.05  --sat_out_clauses                       false
% 0.43/1.05  
% 0.43/1.05  ------ QBF Options
% 0.43/1.05  
% 0.43/1.05  --qbf_mode                              false
% 0.43/1.05  --qbf_elim_univ                         false
% 0.43/1.05  --qbf_dom_inst                          none
% 0.43/1.05  --qbf_dom_pre_inst                      false
% 0.43/1.05  --qbf_sk_in                             false
% 0.43/1.05  --qbf_pred_elim                         true
% 0.43/1.05  --qbf_split                             512
% 0.43/1.05  
% 0.43/1.05  ------ BMC1 Options
% 0.43/1.05  
% 0.43/1.05  --bmc1_incremental                      false
% 0.43/1.05  --bmc1_axioms                           reachable_all
% 0.43/1.05  --bmc1_min_bound                        0
% 0.43/1.05  --bmc1_max_bound                        -1
% 0.43/1.05  --bmc1_max_bound_default                -1
% 0.43/1.05  --bmc1_symbol_reachability              true
% 0.43/1.05  --bmc1_property_lemmas                  false
% 0.43/1.05  --bmc1_k_induction                      false
% 0.43/1.05  --bmc1_non_equiv_states                 false
% 0.43/1.05  --bmc1_deadlock                         false
% 0.43/1.05  --bmc1_ucm                              false
% 0.43/1.05  --bmc1_add_unsat_core                   none
% 0.43/1.05  --bmc1_unsat_core_children              false
% 0.43/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.43/1.05  --bmc1_out_stat                         full
% 0.43/1.05  --bmc1_ground_init                      false
% 0.43/1.05  --bmc1_pre_inst_next_state              false
% 0.43/1.05  --bmc1_pre_inst_state                   false
% 0.43/1.05  --bmc1_pre_inst_reach_state             false
% 0.43/1.05  --bmc1_out_unsat_core                   false
% 0.43/1.05  --bmc1_aig_witness_out                  false
% 0.43/1.05  --bmc1_verbose                          false
% 0.43/1.05  --bmc1_dump_clauses_tptp                false
% 0.43/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.43/1.05  --bmc1_dump_file                        -
% 0.43/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.43/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.43/1.05  --bmc1_ucm_extend_mode                  1
% 0.43/1.05  --bmc1_ucm_init_mode                    2
% 0.43/1.05  --bmc1_ucm_cone_mode                    none
% 0.43/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.43/1.05  --bmc1_ucm_relax_model                  4
% 0.43/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.43/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.43/1.05  --bmc1_ucm_layered_model                none
% 0.43/1.05  --bmc1_ucm_max_lemma_size               10
% 0.43/1.05  
% 0.43/1.05  ------ AIG Options
% 0.43/1.05  
% 0.43/1.05  --aig_mode                              false
% 0.43/1.05  
% 0.43/1.05  ------ Instantiation Options
% 0.43/1.05  
% 0.43/1.05  --instantiation_flag                    true
% 0.43/1.05  --inst_sos_flag                         false
% 0.43/1.05  --inst_sos_phase                        true
% 0.43/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.43/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.43/1.05  --inst_lit_sel_side                     num_symb
% 0.43/1.05  --inst_solver_per_active                1400
% 0.43/1.05  --inst_solver_calls_frac                1.
% 0.43/1.05  --inst_passive_queue_type               priority_queues
% 0.43/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.43/1.05  --inst_passive_queues_freq              [25;2]
% 0.43/1.05  --inst_dismatching                      true
% 0.43/1.05  --inst_eager_unprocessed_to_passive     true
% 0.43/1.05  --inst_prop_sim_given                   true
% 0.43/1.05  --inst_prop_sim_new                     false
% 0.43/1.05  --inst_subs_new                         false
% 0.43/1.05  --inst_eq_res_simp                      false
% 0.43/1.05  --inst_subs_given                       false
% 0.43/1.05  --inst_orphan_elimination               true
% 0.43/1.05  --inst_learning_loop_flag               true
% 0.43/1.05  --inst_learning_start                   3000
% 0.43/1.05  --inst_learning_factor                  2
% 0.43/1.05  --inst_start_prop_sim_after_learn       3
% 0.43/1.05  --inst_sel_renew                        solver
% 0.43/1.05  --inst_lit_activity_flag                true
% 0.43/1.05  --inst_restr_to_given                   false
% 0.43/1.05  --inst_activity_threshold               500
% 0.43/1.05  --inst_out_proof                        true
% 0.43/1.05  
% 0.43/1.05  ------ Resolution Options
% 0.43/1.05  
% 0.43/1.05  --resolution_flag                       true
% 0.43/1.05  --res_lit_sel                           adaptive
% 0.43/1.05  --res_lit_sel_side                      none
% 0.43/1.05  --res_ordering                          kbo
% 0.43/1.05  --res_to_prop_solver                    active
% 0.43/1.05  --res_prop_simpl_new                    false
% 0.43/1.05  --res_prop_simpl_given                  true
% 0.43/1.05  --res_passive_queue_type                priority_queues
% 0.43/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.43/1.05  --res_passive_queues_freq               [15;5]
% 0.43/1.05  --res_forward_subs                      full
% 0.43/1.05  --res_backward_subs                     full
% 0.43/1.05  --res_forward_subs_resolution           true
% 0.43/1.05  --res_backward_subs_resolution          true
% 0.43/1.05  --res_orphan_elimination                true
% 0.43/1.05  --res_time_limit                        2.
% 0.43/1.05  --res_out_proof                         true
% 0.43/1.05  
% 0.43/1.05  ------ Superposition Options
% 0.43/1.05  
% 0.43/1.05  --superposition_flag                    true
% 0.43/1.05  --sup_passive_queue_type                priority_queues
% 0.43/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.43/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.43/1.05  --demod_completeness_check              fast
% 0.43/1.05  --demod_use_ground                      true
% 0.43/1.05  --sup_to_prop_solver                    passive
% 0.43/1.05  --sup_prop_simpl_new                    true
% 0.43/1.05  --sup_prop_simpl_given                  true
% 0.43/1.05  --sup_fun_splitting                     false
% 0.43/1.05  --sup_smt_interval                      50000
% 0.43/1.05  
% 0.43/1.05  ------ Superposition Simplification Setup
% 0.43/1.05  
% 0.43/1.05  --sup_indices_passive                   []
% 0.43/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.43/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.43/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.43/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.43/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.43/1.05  --sup_full_bw                           [BwDemod]
% 0.43/1.05  --sup_immed_triv                        [TrivRules]
% 0.43/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.43/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.43/1.05  --sup_immed_bw_main                     []
% 0.43/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.43/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.43/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.43/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.43/1.05  
% 0.43/1.05  ------ Combination Options
% 0.43/1.05  
% 0.43/1.05  --comb_res_mult                         3
% 0.43/1.05  --comb_sup_mult                         2
% 0.43/1.05  --comb_inst_mult                        10
% 0.43/1.05  
% 0.43/1.05  ------ Debug Options
% 0.43/1.05  
% 0.43/1.05  --dbg_backtrace                         false
% 0.43/1.05  --dbg_dump_prop_clauses                 false
% 0.43/1.05  --dbg_dump_prop_clauses_file            -
% 0.43/1.05  --dbg_out_stat                          false
% 0.43/1.05  ------ Parsing...
% 0.43/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.43/1.05  
% 0.43/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.43/1.05  
% 0.43/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.43/1.05  
% 0.43/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.43/1.05  ------ Proving...
% 0.43/1.05  ------ Problem Properties 
% 0.43/1.05  
% 0.43/1.05  
% 0.43/1.05  clauses                                 7
% 0.43/1.05  conjectures                             2
% 0.43/1.05  EPR                                     0
% 0.43/1.05  Horn                                    7
% 0.43/1.05  unary                                   3
% 0.43/1.05  binary                                  4
% 0.43/1.05  lits                                    11
% 0.43/1.05  lits eq                                 5
% 0.43/1.05  fd_pure                                 0
% 0.43/1.05  fd_pseudo                               0
% 0.43/1.05  fd_cond                                 0
% 0.43/1.05  fd_pseudo_cond                          0
% 0.43/1.05  AC symbols                              0
% 0.43/1.05  
% 0.43/1.05  ------ Schedule dynamic 5 is on 
% 0.43/1.05  
% 0.43/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.43/1.05  
% 0.43/1.05  
% 0.43/1.05  ------ 
% 0.43/1.05  Current options:
% 0.43/1.05  ------ 
% 0.43/1.05  
% 0.43/1.05  ------ Input Options
% 0.43/1.05  
% 0.43/1.05  --out_options                           all
% 0.43/1.05  --tptp_safe_out                         true
% 0.43/1.05  --problem_path                          ""
% 0.43/1.05  --include_path                          ""
% 0.43/1.05  --clausifier                            res/vclausify_rel
% 0.43/1.05  --clausifier_options                    --mode clausify
% 0.43/1.05  --stdin                                 false
% 0.43/1.05  --stats_out                             all
% 0.43/1.05  
% 0.43/1.05  ------ General Options
% 0.43/1.05  
% 0.43/1.05  --fof                                   false
% 0.43/1.05  --time_out_real                         305.
% 0.43/1.05  --time_out_virtual                      -1.
% 0.43/1.05  --symbol_type_check                     false
% 0.43/1.05  --clausify_out                          false
% 0.43/1.05  --sig_cnt_out                           false
% 0.43/1.05  --trig_cnt_out                          false
% 0.43/1.05  --trig_cnt_out_tolerance                1.
% 0.43/1.05  --trig_cnt_out_sk_spl                   false
% 0.43/1.05  --abstr_cl_out                          false
% 0.43/1.05  
% 0.43/1.05  ------ Global Options
% 0.43/1.05  
% 0.43/1.05  --schedule                              default
% 0.43/1.05  --add_important_lit                     false
% 0.43/1.05  --prop_solver_per_cl                    1000
% 0.43/1.05  --min_unsat_core                        false
% 0.43/1.05  --soft_assumptions                      false
% 0.43/1.05  --soft_lemma_size                       3
% 0.43/1.05  --prop_impl_unit_size                   0
% 0.43/1.05  --prop_impl_unit                        []
% 0.43/1.05  --share_sel_clauses                     true
% 0.43/1.05  --reset_solvers                         false
% 0.43/1.05  --bc_imp_inh                            [conj_cone]
% 0.43/1.05  --conj_cone_tolerance                   3.
% 0.43/1.05  --extra_neg_conj                        none
% 0.43/1.05  --large_theory_mode                     true
% 0.43/1.05  --prolific_symb_bound                   200
% 0.43/1.05  --lt_threshold                          2000
% 0.43/1.05  --clause_weak_htbl                      true
% 0.43/1.05  --gc_record_bc_elim                     false
% 0.43/1.05  
% 0.43/1.05  ------ Preprocessing Options
% 0.43/1.05  
% 0.43/1.05  --preprocessing_flag                    true
% 0.43/1.05  --time_out_prep_mult                    0.1
% 0.43/1.05  --splitting_mode                        input
% 0.43/1.05  --splitting_grd                         true
% 0.43/1.05  --splitting_cvd                         false
% 0.43/1.05  --splitting_cvd_svl                     false
% 0.43/1.05  --splitting_nvd                         32
% 0.43/1.05  --sub_typing                            true
% 0.43/1.05  --prep_gs_sim                           true
% 0.43/1.05  --prep_unflatten                        true
% 0.43/1.05  --prep_res_sim                          true
% 0.43/1.05  --prep_upred                            true
% 0.43/1.05  --prep_sem_filter                       exhaustive
% 0.43/1.05  --prep_sem_filter_out                   false
% 0.43/1.05  --pred_elim                             true
% 0.43/1.05  --res_sim_input                         true
% 0.43/1.05  --eq_ax_congr_red                       true
% 0.43/1.05  --pure_diseq_elim                       true
% 0.43/1.05  --brand_transform                       false
% 0.43/1.05  --non_eq_to_eq                          false
% 0.43/1.05  --prep_def_merge                        true
% 0.43/1.05  --prep_def_merge_prop_impl              false
% 0.43/1.05  --prep_def_merge_mbd                    true
% 0.43/1.05  --prep_def_merge_tr_red                 false
% 0.43/1.05  --prep_def_merge_tr_cl                  false
% 0.43/1.05  --smt_preprocessing                     true
% 0.43/1.05  --smt_ac_axioms                         fast
% 0.43/1.05  --preprocessed_out                      false
% 0.43/1.05  --preprocessed_stats                    false
% 0.43/1.05  
% 0.43/1.05  ------ Abstraction refinement Options
% 0.43/1.05  
% 0.43/1.05  --abstr_ref                             []
% 0.43/1.05  --abstr_ref_prep                        false
% 0.43/1.05  --abstr_ref_until_sat                   false
% 0.43/1.05  --abstr_ref_sig_restrict                funpre
% 0.43/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.43/1.05  --abstr_ref_under                       []
% 0.43/1.05  
% 0.43/1.05  ------ SAT Options
% 0.43/1.05  
% 0.43/1.05  --sat_mode                              false
% 0.43/1.05  --sat_fm_restart_options                ""
% 0.43/1.05  --sat_gr_def                            false
% 0.43/1.05  --sat_epr_types                         true
% 0.43/1.05  --sat_non_cyclic_types                  false
% 0.43/1.05  --sat_finite_models                     false
% 0.43/1.05  --sat_fm_lemmas                         false
% 0.43/1.05  --sat_fm_prep                           false
% 0.43/1.05  --sat_fm_uc_incr                        true
% 0.43/1.05  --sat_out_model                         small
% 0.43/1.05  --sat_out_clauses                       false
% 0.43/1.05  
% 0.43/1.05  ------ QBF Options
% 0.43/1.05  
% 0.43/1.05  --qbf_mode                              false
% 0.43/1.05  --qbf_elim_univ                         false
% 0.43/1.05  --qbf_dom_inst                          none
% 0.43/1.05  --qbf_dom_pre_inst                      false
% 0.43/1.05  --qbf_sk_in                             false
% 0.43/1.05  --qbf_pred_elim                         true
% 0.43/1.05  --qbf_split                             512
% 0.43/1.05  
% 0.43/1.05  ------ BMC1 Options
% 0.43/1.05  
% 0.43/1.05  --bmc1_incremental                      false
% 0.43/1.05  --bmc1_axioms                           reachable_all
% 0.43/1.05  --bmc1_min_bound                        0
% 0.43/1.05  --bmc1_max_bound                        -1
% 0.43/1.05  --bmc1_max_bound_default                -1
% 0.43/1.05  --bmc1_symbol_reachability              true
% 1.10/1.05  --bmc1_property_lemmas                  false
% 1.10/1.05  --bmc1_k_induction                      false
% 1.10/1.05  --bmc1_non_equiv_states                 false
% 1.10/1.05  --bmc1_deadlock                         false
% 1.10/1.05  --bmc1_ucm                              false
% 1.10/1.05  --bmc1_add_unsat_core                   none
% 1.10/1.05  --bmc1_unsat_core_children              false
% 1.10/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/1.05  --bmc1_out_stat                         full
% 1.10/1.05  --bmc1_ground_init                      false
% 1.10/1.05  --bmc1_pre_inst_next_state              false
% 1.10/1.05  --bmc1_pre_inst_state                   false
% 1.10/1.05  --bmc1_pre_inst_reach_state             false
% 1.10/1.05  --bmc1_out_unsat_core                   false
% 1.10/1.05  --bmc1_aig_witness_out                  false
% 1.10/1.05  --bmc1_verbose                          false
% 1.10/1.05  --bmc1_dump_clauses_tptp                false
% 1.10/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.10/1.05  --bmc1_dump_file                        -
% 1.10/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.10/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.10/1.05  --bmc1_ucm_extend_mode                  1
% 1.10/1.05  --bmc1_ucm_init_mode                    2
% 1.10/1.05  --bmc1_ucm_cone_mode                    none
% 1.10/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.10/1.05  --bmc1_ucm_relax_model                  4
% 1.10/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.10/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/1.05  --bmc1_ucm_layered_model                none
% 1.10/1.05  --bmc1_ucm_max_lemma_size               10
% 1.10/1.05  
% 1.10/1.05  ------ AIG Options
% 1.10/1.05  
% 1.10/1.05  --aig_mode                              false
% 1.10/1.05  
% 1.10/1.05  ------ Instantiation Options
% 1.10/1.05  
% 1.10/1.05  --instantiation_flag                    true
% 1.10/1.05  --inst_sos_flag                         false
% 1.10/1.05  --inst_sos_phase                        true
% 1.10/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/1.05  --inst_lit_sel_side                     none
% 1.10/1.05  --inst_solver_per_active                1400
% 1.10/1.05  --inst_solver_calls_frac                1.
% 1.10/1.05  --inst_passive_queue_type               priority_queues
% 1.10/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/1.05  --inst_passive_queues_freq              [25;2]
% 1.10/1.05  --inst_dismatching                      true
% 1.10/1.05  --inst_eager_unprocessed_to_passive     true
% 1.10/1.05  --inst_prop_sim_given                   true
% 1.10/1.05  --inst_prop_sim_new                     false
% 1.10/1.05  --inst_subs_new                         false
% 1.10/1.05  --inst_eq_res_simp                      false
% 1.10/1.05  --inst_subs_given                       false
% 1.10/1.05  --inst_orphan_elimination               true
% 1.10/1.05  --inst_learning_loop_flag               true
% 1.10/1.05  --inst_learning_start                   3000
% 1.10/1.05  --inst_learning_factor                  2
% 1.10/1.05  --inst_start_prop_sim_after_learn       3
% 1.10/1.05  --inst_sel_renew                        solver
% 1.10/1.05  --inst_lit_activity_flag                true
% 1.10/1.05  --inst_restr_to_given                   false
% 1.10/1.05  --inst_activity_threshold               500
% 1.10/1.05  --inst_out_proof                        true
% 1.10/1.05  
% 1.10/1.05  ------ Resolution Options
% 1.10/1.05  
% 1.10/1.05  --resolution_flag                       false
% 1.10/1.05  --res_lit_sel                           adaptive
% 1.10/1.05  --res_lit_sel_side                      none
% 1.10/1.05  --res_ordering                          kbo
% 1.10/1.05  --res_to_prop_solver                    active
% 1.10/1.05  --res_prop_simpl_new                    false
% 1.10/1.05  --res_prop_simpl_given                  true
% 1.10/1.05  --res_passive_queue_type                priority_queues
% 1.10/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/1.05  --res_passive_queues_freq               [15;5]
% 1.10/1.05  --res_forward_subs                      full
% 1.10/1.05  --res_backward_subs                     full
% 1.10/1.05  --res_forward_subs_resolution           true
% 1.10/1.05  --res_backward_subs_resolution          true
% 1.10/1.05  --res_orphan_elimination                true
% 1.10/1.05  --res_time_limit                        2.
% 1.10/1.05  --res_out_proof                         true
% 1.10/1.05  
% 1.10/1.05  ------ Superposition Options
% 1.10/1.05  
% 1.10/1.05  --superposition_flag                    true
% 1.10/1.05  --sup_passive_queue_type                priority_queues
% 1.10/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.10/1.05  --demod_completeness_check              fast
% 1.10/1.05  --demod_use_ground                      true
% 1.10/1.05  --sup_to_prop_solver                    passive
% 1.10/1.05  --sup_prop_simpl_new                    true
% 1.10/1.05  --sup_prop_simpl_given                  true
% 1.10/1.05  --sup_fun_splitting                     false
% 1.10/1.05  --sup_smt_interval                      50000
% 1.10/1.05  
% 1.10/1.05  ------ Superposition Simplification Setup
% 1.10/1.05  
% 1.10/1.05  --sup_indices_passive                   []
% 1.10/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.05  --sup_full_bw                           [BwDemod]
% 1.10/1.05  --sup_immed_triv                        [TrivRules]
% 1.10/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.05  --sup_immed_bw_main                     []
% 1.10/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.05  
% 1.10/1.05  ------ Combination Options
% 1.10/1.05  
% 1.10/1.05  --comb_res_mult                         3
% 1.10/1.05  --comb_sup_mult                         2
% 1.10/1.05  --comb_inst_mult                        10
% 1.10/1.05  
% 1.10/1.05  ------ Debug Options
% 1.10/1.05  
% 1.10/1.05  --dbg_backtrace                         false
% 1.10/1.05  --dbg_dump_prop_clauses                 false
% 1.10/1.05  --dbg_dump_prop_clauses_file            -
% 1.10/1.05  --dbg_out_stat                          false
% 1.10/1.05  
% 1.10/1.05  
% 1.10/1.05  
% 1.10/1.05  
% 1.10/1.05  ------ Proving...
% 1.10/1.05  
% 1.10/1.05  
% 1.10/1.05  % SZS status Theorem for theBenchmark.p
% 1.10/1.05  
% 1.10/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.10/1.05  
% 1.10/1.05  fof(f6,conjecture,(
% 1.10/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)))))),
% 1.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.05  
% 1.10/1.05  fof(f7,negated_conjecture,(
% 1.10/1.05    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)))))),
% 1.10/1.05    inference(negated_conjecture,[],[f6])).
% 1.10/1.05  
% 1.10/1.05  fof(f16,plain,(
% 1.10/1.05    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1)) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.10/1.05    inference(ennf_transformation,[],[f7])).
% 1.10/1.05  
% 1.10/1.05  fof(f17,plain,(
% 1.10/1.05    ? [X0] : (? [X1] : (k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1)) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.10/1.05    inference(flattening,[],[f16])).
% 1.10/1.05  
% 1.10/1.05  fof(f20,plain,(
% 1.10/1.05    ( ! [X0] : (? [X1] : (k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1)) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_tops_1(X0,sK1) != k2_tops_1(X0,k1_tops_1(X0,sK1)) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.10/1.05    introduced(choice_axiom,[])).
% 1.10/1.05  
% 1.10/1.05  fof(f19,plain,(
% 1.10/1.05    ? [X0] : (? [X1] : (k2_tops_1(X0,X1) != k2_tops_1(X0,k1_tops_1(X0,X1)) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,X1) != k2_tops_1(sK0,k1_tops_1(sK0,X1)) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.10/1.05    introduced(choice_axiom,[])).
% 1.10/1.05  
% 1.10/1.05  fof(f21,plain,(
% 1.10/1.05    (k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1)) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.10/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20,f19])).
% 1.10/1.05  
% 1.10/1.05  fof(f29,plain,(
% 1.10/1.05    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.10/1.05    inference(cnf_transformation,[],[f21])).
% 1.10/1.05  
% 1.10/1.05  fof(f3,axiom,(
% 1.10/1.05    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.05  
% 1.10/1.05  fof(f11,plain,(
% 1.10/1.05    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.10/1.05    inference(ennf_transformation,[],[f3])).
% 1.10/1.05  
% 1.10/1.05  fof(f12,plain,(
% 1.10/1.05    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.10/1.05    inference(flattening,[],[f11])).
% 1.10/1.05  
% 1.10/1.05  fof(f25,plain,(
% 1.10/1.05    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.10/1.05    inference(cnf_transformation,[],[f12])).
% 1.10/1.05  
% 1.10/1.05  fof(f28,plain,(
% 1.10/1.05    l1_pre_topc(sK0)),
% 1.10/1.05    inference(cnf_transformation,[],[f21])).
% 1.10/1.05  
% 1.10/1.05  fof(f4,axiom,(
% 1.10/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.05  
% 1.10/1.05  fof(f13,plain,(
% 1.10/1.05    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/1.05    inference(ennf_transformation,[],[f4])).
% 1.10/1.05  
% 1.10/1.05  fof(f26,plain,(
% 1.10/1.05    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.10/1.05    inference(cnf_transformation,[],[f13])).
% 1.10/1.05  
% 1.10/1.05  fof(f2,axiom,(
% 1.10/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.05  
% 1.10/1.05  fof(f10,plain,(
% 1.10/1.05    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/1.05    inference(ennf_transformation,[],[f2])).
% 1.10/1.05  
% 1.10/1.05  fof(f18,plain,(
% 1.10/1.05    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/1.05    inference(nnf_transformation,[],[f10])).
% 1.10/1.05  
% 1.10/1.05  fof(f23,plain,(
% 1.10/1.05    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.10/1.05    inference(cnf_transformation,[],[f18])).
% 1.10/1.05  
% 1.10/1.05  fof(f30,plain,(
% 1.10/1.05    v5_tops_1(sK1,sK0)),
% 1.10/1.05    inference(cnf_transformation,[],[f21])).
% 1.10/1.05  
% 1.10/1.05  fof(f5,axiom,(
% 1.10/1.05    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 1.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.05  
% 1.10/1.05  fof(f14,plain,(
% 1.10/1.05    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.10/1.05    inference(ennf_transformation,[],[f5])).
% 1.10/1.05  
% 1.10/1.05  fof(f15,plain,(
% 1.10/1.05    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.10/1.05    inference(flattening,[],[f14])).
% 1.10/1.05  
% 1.10/1.05  fof(f27,plain,(
% 1.10/1.05    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.10/1.05    inference(cnf_transformation,[],[f15])).
% 1.10/1.05  
% 1.10/1.05  fof(f1,axiom,(
% 1.10/1.05    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 1.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.05  
% 1.10/1.05  fof(f8,plain,(
% 1.10/1.05    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.10/1.05    inference(ennf_transformation,[],[f1])).
% 1.10/1.05  
% 1.10/1.05  fof(f9,plain,(
% 1.10/1.05    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.10/1.05    inference(flattening,[],[f8])).
% 1.10/1.05  
% 1.10/1.05  fof(f22,plain,(
% 1.10/1.05    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.10/1.05    inference(cnf_transformation,[],[f9])).
% 1.10/1.05  
% 1.10/1.05  fof(f31,plain,(
% 1.10/1.05    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 1.10/1.05    inference(cnf_transformation,[],[f21])).
% 1.10/1.05  
% 1.10/1.05  cnf(c_8,negated_conjecture,
% 1.10/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.10/1.05      inference(cnf_transformation,[],[f29]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_225,negated_conjecture,
% 1.10/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.10/1.05      inference(subtyping,[status(esa)],[c_8]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_344,plain,
% 1.10/1.05      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.10/1.05      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_3,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | ~ l1_pre_topc(X1) ),
% 1.10/1.05      inference(cnf_transformation,[],[f25]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_9,negated_conjecture,
% 1.10/1.05      ( l1_pre_topc(sK0) ),
% 1.10/1.05      inference(cnf_transformation,[],[f28]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_140,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | sK0 != X1 ),
% 1.10/1.05      inference(resolution_lifted,[status(thm)],[c_3,c_9]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_141,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.10/1.05      inference(unflattening,[status(thm)],[c_140]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_221,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | m1_subset_1(k1_tops_1(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.10/1.05      inference(subtyping,[status(esa)],[c_141]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_347,plain,
% 1.10/1.05      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.10/1.05      | m1_subset_1(k1_tops_1(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.10/1.05      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_4,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | ~ l1_pre_topc(X1)
% 1.10/1.05      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 1.10/1.05      inference(cnf_transformation,[],[f26]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_128,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 1.10/1.05      | sK0 != X1 ),
% 1.10/1.05      inference(resolution_lifted,[status(thm)],[c_4,c_9]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_129,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 1.10/1.05      inference(unflattening,[status(thm)],[c_128]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_222,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_39),k1_tops_1(sK0,X0_39)) = k2_tops_1(sK0,X0_39) ),
% 1.10/1.05      inference(subtyping,[status(esa)],[c_129]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_346,plain,
% 1.10/1.05      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_39),k1_tops_1(sK0,X0_39)) = k2_tops_1(sK0,X0_39)
% 1.10/1.05      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.10/1.05      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_559,plain,
% 1.10/1.05      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,X0_39)),k1_tops_1(sK0,k1_tops_1(sK0,X0_39))) = k2_tops_1(sK0,k1_tops_1(sK0,X0_39))
% 1.10/1.05      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.10/1.05      inference(superposition,[status(thm)],[c_347,c_346]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_890,plain,
% 1.10/1.05      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 1.10/1.05      inference(superposition,[status(thm)],[c_344,c_559]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_2,plain,
% 1.10/1.05      ( ~ v5_tops_1(X0,X1)
% 1.10/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | ~ l1_pre_topc(X1)
% 1.10/1.05      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 1.10/1.05      inference(cnf_transformation,[],[f23]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_7,negated_conjecture,
% 1.10/1.05      ( v5_tops_1(sK1,sK0) ),
% 1.10/1.05      inference(cnf_transformation,[],[f30]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_107,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | ~ l1_pre_topc(X1)
% 1.10/1.05      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 1.10/1.05      | sK1 != X0
% 1.10/1.05      | sK0 != X1 ),
% 1.10/1.05      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_108,plain,
% 1.10/1.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | ~ l1_pre_topc(sK0)
% 1.10/1.05      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 1.10/1.05      inference(unflattening,[status(thm)],[c_107]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_110,plain,
% 1.10/1.05      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 1.10/1.05      inference(global_propositional_subsumption,
% 1.10/1.05                [status(thm)],
% 1.10/1.05                [c_108,c_9,c_8]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_224,plain,
% 1.10/1.05      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 1.10/1.05      inference(subtyping,[status(esa)],[c_110]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_5,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | ~ l1_pre_topc(X1)
% 1.10/1.05      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 1.10/1.05      inference(cnf_transformation,[],[f27]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_116,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 1.10/1.05      | sK0 != X1 ),
% 1.10/1.05      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_117,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 1.10/1.05      inference(unflattening,[status(thm)],[c_116]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_223,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | k1_tops_1(sK0,k1_tops_1(sK0,X0_39)) = k1_tops_1(sK0,X0_39) ),
% 1.10/1.05      inference(subtyping,[status(esa)],[c_117]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_345,plain,
% 1.10/1.05      ( k1_tops_1(sK0,k1_tops_1(sK0,X0_39)) = k1_tops_1(sK0,X0_39)
% 1.10/1.05      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.10/1.05      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_408,plain,
% 1.10/1.05      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 1.10/1.05      inference(superposition,[status(thm)],[c_344,c_345]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_0,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | ~ l1_pre_topc(X1)
% 1.10/1.05      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 1.10/1.05      inference(cnf_transformation,[],[f22]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_152,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.05      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 1.10/1.05      | sK0 != X1 ),
% 1.10/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_153,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 1.10/1.05      inference(unflattening,[status(thm)],[c_152]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_220,plain,
% 1.10/1.05      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.10/1.05      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0_39)) = k2_pre_topc(sK0,X0_39) ),
% 1.10/1.05      inference(subtyping,[status(esa)],[c_153]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_348,plain,
% 1.10/1.05      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0_39)) = k2_pre_topc(sK0,X0_39)
% 1.10/1.05      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.10/1.05      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_497,plain,
% 1.10/1.05      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_39))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_39))
% 1.10/1.05      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.10/1.05      inference(superposition,[status(thm)],[c_347,c_348]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_633,plain,
% 1.10/1.05      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 1.10/1.05      inference(superposition,[status(thm)],[c_344,c_497]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_640,plain,
% 1.10/1.05      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 1.10/1.05      inference(light_normalisation,[status(thm)],[c_633,c_224]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_558,plain,
% 1.10/1.05      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 1.10/1.05      inference(superposition,[status(thm)],[c_344,c_346]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_712,plain,
% 1.10/1.05      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 1.10/1.05      inference(demodulation,[status(thm)],[c_640,c_558]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_897,plain,
% 1.10/1.05      ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 1.10/1.05      inference(light_normalisation,
% 1.10/1.05                [status(thm)],
% 1.10/1.05                [c_890,c_224,c_408,c_712]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_231,plain,
% 1.10/1.05      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 1.10/1.05      theory(equality) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_384,plain,
% 1.10/1.05      ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != X0_43
% 1.10/1.05      | k2_tops_1(sK0,sK1) != X0_43
% 1.10/1.05      | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 1.10/1.05      inference(instantiation,[status(thm)],[c_231]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_395,plain,
% 1.10/1.05      ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 1.10/1.05      | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
% 1.10/1.05      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 1.10/1.05      inference(instantiation,[status(thm)],[c_384]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_6,negated_conjecture,
% 1.10/1.05      ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 1.10/1.05      inference(cnf_transformation,[],[f31]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_226,negated_conjecture,
% 1.10/1.05      ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 1.10/1.05      inference(subtyping,[status(esa)],[c_6]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_228,plain,( X0_39 = X0_39 ),theory(equality) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_243,plain,
% 1.10/1.05      ( sK1 = sK1 ),
% 1.10/1.05      inference(instantiation,[status(thm)],[c_228]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_235,plain,
% 1.10/1.05      ( k2_tops_1(X0_42,X0_39) = k2_tops_1(X0_42,X1_39)
% 1.10/1.05      | X0_39 != X1_39 ),
% 1.10/1.05      theory(equality) ).
% 1.10/1.05  
% 1.10/1.05  cnf(c_240,plain,
% 1.10/1.05      ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1) | sK1 != sK1 ),
% 1.10/1.05      inference(instantiation,[status(thm)],[c_235]) ).
% 1.10/1.05  
% 1.10/1.05  cnf(contradiction,plain,
% 1.10/1.05      ( $false ),
% 1.10/1.05      inference(minisat,[status(thm)],[c_897,c_395,c_226,c_243,c_240]) ).
% 1.10/1.05  
% 1.10/1.05  
% 1.10/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.10/1.05  
% 1.10/1.05  ------                               Statistics
% 1.10/1.05  
% 1.10/1.05  ------ General
% 1.10/1.05  
% 1.10/1.05  abstr_ref_over_cycles:                  0
% 1.10/1.05  abstr_ref_under_cycles:                 0
% 1.10/1.05  gc_basic_clause_elim:                   0
% 1.10/1.05  forced_gc_time:                         0
% 1.10/1.05  parsing_time:                           0.014
% 1.10/1.05  unif_index_cands_time:                  0.
% 1.10/1.05  unif_index_add_time:                    0.
% 1.10/1.05  orderings_time:                         0.
% 1.10/1.05  out_proof_time:                         0.012
% 1.10/1.05  total_time:                             0.083
% 1.10/1.05  num_of_symbols:                         44
% 1.10/1.05  num_of_terms:                           738
% 1.10/1.05  
% 1.10/1.05  ------ Preprocessing
% 1.10/1.05  
% 1.10/1.05  num_of_splits:                          0
% 1.10/1.05  num_of_split_atoms:                     0
% 1.10/1.05  num_of_reused_defs:                     0
% 1.10/1.05  num_eq_ax_congr_red:                    8
% 1.10/1.05  num_of_sem_filtered_clauses:            1
% 1.10/1.05  num_of_subtypes:                        5
% 1.10/1.05  monotx_restored_types:                  0
% 1.10/1.05  sat_num_of_epr_types:                   0
% 1.10/1.05  sat_num_of_non_cyclic_types:            0
% 1.10/1.05  sat_guarded_non_collapsed_types:        0
% 1.10/1.05  num_pure_diseq_elim:                    0
% 1.10/1.05  simp_replaced_by:                       0
% 1.10/1.05  res_preprocessed:                       50
% 1.10/1.05  prep_upred:                             0
% 1.10/1.05  prep_unflattend:                        6
% 1.10/1.05  smt_new_axioms:                         0
% 1.10/1.05  pred_elim_cands:                        1
% 1.10/1.05  pred_elim:                              2
% 1.10/1.05  pred_elim_cl:                           3
% 1.10/1.05  pred_elim_cycles:                       4
% 1.10/1.05  merged_defs:                            0
% 1.10/1.05  merged_defs_ncl:                        0
% 1.10/1.05  bin_hyper_res:                          0
% 1.10/1.05  prep_cycles:                            4
% 1.10/1.05  pred_elim_time:                         0.002
% 1.10/1.05  splitting_time:                         0.
% 1.10/1.05  sem_filter_time:                        0.
% 1.10/1.05  monotx_time:                            0.
% 1.10/1.05  subtype_inf_time:                       0.
% 1.10/1.05  
% 1.10/1.05  ------ Problem properties
% 1.10/1.05  
% 1.10/1.05  clauses:                                7
% 1.10/1.05  conjectures:                            2
% 1.10/1.05  epr:                                    0
% 1.10/1.05  horn:                                   7
% 1.10/1.05  ground:                                 3
% 1.10/1.05  unary:                                  3
% 1.10/1.05  binary:                                 4
% 1.10/1.05  lits:                                   11
% 1.10/1.05  lits_eq:                                5
% 1.10/1.05  fd_pure:                                0
% 1.10/1.05  fd_pseudo:                              0
% 1.10/1.05  fd_cond:                                0
% 1.10/1.05  fd_pseudo_cond:                         0
% 1.10/1.05  ac_symbols:                             0
% 1.10/1.05  
% 1.10/1.05  ------ Propositional Solver
% 1.10/1.05  
% 1.10/1.05  prop_solver_calls:                      27
% 1.10/1.05  prop_fast_solver_calls:                 234
% 1.10/1.05  smt_solver_calls:                       0
% 1.10/1.05  smt_fast_solver_calls:                  0
% 1.10/1.05  prop_num_of_clauses:                    260
% 1.10/1.05  prop_preprocess_simplified:             1399
% 1.10/1.05  prop_fo_subsumed:                       2
% 1.10/1.05  prop_solver_time:                       0.
% 1.10/1.05  smt_solver_time:                        0.
% 1.10/1.05  smt_fast_solver_time:                   0.
% 1.10/1.05  prop_fast_solver_time:                  0.
% 1.10/1.05  prop_unsat_core_time:                   0.
% 1.10/1.05  
% 1.10/1.05  ------ QBF
% 1.10/1.05  
% 1.10/1.05  qbf_q_res:                              0
% 1.10/1.05  qbf_num_tautologies:                    0
% 1.10/1.05  qbf_prep_cycles:                        0
% 1.10/1.05  
% 1.10/1.05  ------ BMC1
% 1.10/1.05  
% 1.10/1.05  bmc1_current_bound:                     -1
% 1.10/1.05  bmc1_last_solved_bound:                 -1
% 1.10/1.05  bmc1_unsat_core_size:                   -1
% 1.10/1.05  bmc1_unsat_core_parents_size:           -1
% 1.10/1.05  bmc1_merge_next_fun:                    0
% 1.10/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.10/1.05  
% 1.10/1.05  ------ Instantiation
% 1.10/1.05  
% 1.10/1.05  inst_num_of_clauses:                    130
% 1.10/1.05  inst_num_in_passive:                    14
% 1.10/1.05  inst_num_in_active:                     84
% 1.10/1.05  inst_num_in_unprocessed:                32
% 1.10/1.05  inst_num_of_loops:                      90
% 1.10/1.05  inst_num_of_learning_restarts:          0
% 1.10/1.05  inst_num_moves_active_passive:          1
% 1.10/1.05  inst_lit_activity:                      0
% 1.10/1.05  inst_lit_activity_moves:                0
% 1.10/1.05  inst_num_tautologies:                   0
% 1.10/1.05  inst_num_prop_implied:                  0
% 1.10/1.05  inst_num_existing_simplified:           0
% 1.10/1.05  inst_num_eq_res_simplified:             0
% 1.10/1.05  inst_num_child_elim:                    0
% 1.10/1.05  inst_num_of_dismatching_blockings:      32
% 1.10/1.05  inst_num_of_non_proper_insts:           144
% 1.10/1.05  inst_num_of_duplicates:                 0
% 1.10/1.05  inst_inst_num_from_inst_to_res:         0
% 1.10/1.05  inst_dismatching_checking_time:         0.
% 1.10/1.05  
% 1.10/1.05  ------ Resolution
% 1.10/1.05  
% 1.10/1.05  res_num_of_clauses:                     0
% 1.10/1.05  res_num_in_passive:                     0
% 1.10/1.05  res_num_in_active:                      0
% 1.10/1.05  res_num_of_loops:                       54
% 1.10/1.05  res_forward_subset_subsumed:            44
% 1.10/1.05  res_backward_subset_subsumed:           2
% 1.10/1.05  res_forward_subsumed:                   0
% 1.10/1.05  res_backward_subsumed:                  0
% 1.10/1.05  res_forward_subsumption_resolution:     0
% 1.10/1.05  res_backward_subsumption_resolution:    0
% 1.10/1.05  res_clause_to_clause_subsumption:       49
% 1.10/1.05  res_orphan_elimination:                 0
% 1.10/1.05  res_tautology_del:                      23
% 1.10/1.05  res_num_eq_res_simplified:              0
% 1.10/1.05  res_num_sel_changes:                    0
% 1.10/1.05  res_moves_from_active_to_pass:          0
% 1.10/1.05  
% 1.10/1.05  ------ Superposition
% 1.10/1.05  
% 1.10/1.05  sup_time_total:                         0.
% 1.10/1.05  sup_time_generating:                    0.
% 1.10/1.05  sup_time_sim_full:                      0.
% 1.10/1.05  sup_time_sim_immed:                     0.
% 1.10/1.05  
% 1.10/1.05  sup_num_of_clauses:                     19
% 1.10/1.05  sup_num_in_active:                      15
% 1.10/1.05  sup_num_in_passive:                     4
% 1.10/1.05  sup_num_of_loops:                       16
% 1.10/1.05  sup_fw_superposition:                   16
% 1.10/1.05  sup_bw_superposition:                   1
% 1.10/1.05  sup_immediate_simplified:               5
% 1.10/1.05  sup_given_eliminated:                   0
% 1.10/1.05  comparisons_done:                       0
% 1.10/1.05  comparisons_avoided:                    0
% 1.10/1.05  
% 1.10/1.05  ------ Simplifications
% 1.10/1.05  
% 1.10/1.05  
% 1.10/1.05  sim_fw_subset_subsumed:                 0
% 1.10/1.05  sim_bw_subset_subsumed:                 0
% 1.10/1.05  sim_fw_subsumed:                        0
% 1.10/1.05  sim_bw_subsumed:                        0
% 1.10/1.05  sim_fw_subsumption_res:                 0
% 1.10/1.05  sim_bw_subsumption_res:                 0
% 1.10/1.05  sim_tautology_del:                      1
% 1.10/1.05  sim_eq_tautology_del:                   3
% 1.10/1.05  sim_eq_res_simp:                        0
% 1.10/1.05  sim_fw_demodulated:                     0
% 1.10/1.05  sim_bw_demodulated:                     2
% 1.10/1.05  sim_light_normalised:                   5
% 1.10/1.05  sim_joinable_taut:                      0
% 1.10/1.05  sim_joinable_simp:                      0
% 1.10/1.05  sim_ac_normalised:                      0
% 1.10/1.05  sim_smt_subsumption:                    0
% 1.10/1.05  
%------------------------------------------------------------------------------
