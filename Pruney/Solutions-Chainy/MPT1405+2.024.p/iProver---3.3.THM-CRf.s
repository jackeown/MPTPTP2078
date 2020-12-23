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
% DateTime   : Thu Dec  3 12:18:51 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 287 expanded)
%              Number of clauses        :   58 (  89 expanded)
%              Number of leaves         :   12 (  65 expanded)
%              Depth                    :   22
%              Number of atoms          :  284 ( 949 expanded)
%              Number of equality atoms :   58 (  90 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_tops_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_tops_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).

fof(f40,plain,(
    ! [X0] :
      ( v1_tops_1(sK0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m2_connsp_2(k2_struct_0(X0),X0,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f30,f29])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( v1_tops_1(sK0(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_238,plain,
    ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,sK0(X0)) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_242,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,sK0(X0)) = k2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_238,c_8])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_325,plain,
    ( k2_pre_topc(X0,sK0(X0)) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_242,c_14])).

cnf(c_326,plain,
    ( k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_433,plain,
    ( k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_326])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0_43),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_528,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0_43),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_222,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_2])).

cnf(c_330,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_14])).

cnf(c_331,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_432,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_331])).

cnf(c_542,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0_43),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_528,c_432])).

cnf(c_659,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_433,c_542])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_126,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_12,negated_conjecture,
    ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_290,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_291,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_14])).

cnf(c_296,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_295])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_struct_0(sK1) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_296])).

cnf(c_363,plain,
    ( ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_365,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_13])).

cnf(c_366,plain,
    ( ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_struct_0(sK1)) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_126,c_366])).

cnf(c_381,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK1,k2_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_429,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK1,k2_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_529,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK1,k2_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_9,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_258,plain,
    ( ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_259,plain,
    ( ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_27,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_261,plain,
    ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_259,c_15,c_14,c_27])).

cnf(c_434,plain,
    ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_261])).

cnf(c_547,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_529,c_432,c_434])).

cnf(c_435,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_526,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_532,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_526,c_432])).

cnf(c_550,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_547,c_532])).

cnf(c_335,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_336,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_431,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_336])).

cnf(c_527,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_539,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_527,c_432])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_659,c_550,c_539])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.73/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.73/1.04  
% 0.73/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.73/1.04  
% 0.73/1.04  ------  iProver source info
% 0.73/1.04  
% 0.73/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.73/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.73/1.04  git: non_committed_changes: false
% 0.73/1.04  git: last_make_outside_of_git: false
% 0.73/1.04  
% 0.73/1.04  ------ 
% 0.73/1.04  
% 0.73/1.04  ------ Input Options
% 0.73/1.04  
% 0.73/1.04  --out_options                           all
% 0.73/1.04  --tptp_safe_out                         true
% 0.73/1.04  --problem_path                          ""
% 0.73/1.04  --include_path                          ""
% 0.73/1.04  --clausifier                            res/vclausify_rel
% 0.73/1.04  --clausifier_options                    --mode clausify
% 0.73/1.04  --stdin                                 false
% 0.73/1.04  --stats_out                             all
% 0.73/1.04  
% 0.73/1.04  ------ General Options
% 0.73/1.04  
% 0.73/1.04  --fof                                   false
% 0.73/1.04  --time_out_real                         305.
% 0.73/1.04  --time_out_virtual                      -1.
% 0.73/1.04  --symbol_type_check                     false
% 0.73/1.04  --clausify_out                          false
% 0.73/1.04  --sig_cnt_out                           false
% 0.73/1.04  --trig_cnt_out                          false
% 0.73/1.04  --trig_cnt_out_tolerance                1.
% 0.73/1.04  --trig_cnt_out_sk_spl                   false
% 0.73/1.04  --abstr_cl_out                          false
% 0.73/1.04  
% 0.73/1.04  ------ Global Options
% 0.73/1.04  
% 0.73/1.04  --schedule                              default
% 0.73/1.04  --add_important_lit                     false
% 0.73/1.04  --prop_solver_per_cl                    1000
% 0.73/1.04  --min_unsat_core                        false
% 0.73/1.04  --soft_assumptions                      false
% 0.73/1.04  --soft_lemma_size                       3
% 0.73/1.04  --prop_impl_unit_size                   0
% 0.73/1.04  --prop_impl_unit                        []
% 0.73/1.04  --share_sel_clauses                     true
% 0.73/1.04  --reset_solvers                         false
% 0.73/1.04  --bc_imp_inh                            [conj_cone]
% 0.73/1.04  --conj_cone_tolerance                   3.
% 0.73/1.04  --extra_neg_conj                        none
% 0.73/1.04  --large_theory_mode                     true
% 0.73/1.04  --prolific_symb_bound                   200
% 0.73/1.04  --lt_threshold                          2000
% 0.73/1.04  --clause_weak_htbl                      true
% 0.73/1.04  --gc_record_bc_elim                     false
% 0.73/1.04  
% 0.73/1.04  ------ Preprocessing Options
% 0.73/1.04  
% 0.73/1.04  --preprocessing_flag                    true
% 0.73/1.04  --time_out_prep_mult                    0.1
% 0.73/1.04  --splitting_mode                        input
% 0.73/1.04  --splitting_grd                         true
% 0.73/1.04  --splitting_cvd                         false
% 0.73/1.04  --splitting_cvd_svl                     false
% 0.73/1.04  --splitting_nvd                         32
% 0.73/1.04  --sub_typing                            true
% 0.73/1.04  --prep_gs_sim                           true
% 0.73/1.04  --prep_unflatten                        true
% 0.73/1.04  --prep_res_sim                          true
% 0.73/1.04  --prep_upred                            true
% 0.73/1.04  --prep_sem_filter                       exhaustive
% 0.73/1.04  --prep_sem_filter_out                   false
% 0.73/1.04  --pred_elim                             true
% 0.73/1.04  --res_sim_input                         true
% 0.73/1.04  --eq_ax_congr_red                       true
% 0.73/1.04  --pure_diseq_elim                       true
% 0.73/1.04  --brand_transform                       false
% 0.73/1.04  --non_eq_to_eq                          false
% 0.73/1.04  --prep_def_merge                        true
% 0.73/1.04  --prep_def_merge_prop_impl              false
% 0.73/1.04  --prep_def_merge_mbd                    true
% 0.73/1.04  --prep_def_merge_tr_red                 false
% 0.73/1.04  --prep_def_merge_tr_cl                  false
% 0.73/1.04  --smt_preprocessing                     true
% 0.73/1.04  --smt_ac_axioms                         fast
% 0.73/1.04  --preprocessed_out                      false
% 0.73/1.04  --preprocessed_stats                    false
% 0.73/1.04  
% 0.73/1.04  ------ Abstraction refinement Options
% 0.73/1.04  
% 0.73/1.04  --abstr_ref                             []
% 0.73/1.04  --abstr_ref_prep                        false
% 0.73/1.04  --abstr_ref_until_sat                   false
% 0.73/1.04  --abstr_ref_sig_restrict                funpre
% 0.73/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.73/1.04  --abstr_ref_under                       []
% 0.73/1.04  
% 0.73/1.04  ------ SAT Options
% 0.73/1.04  
% 0.73/1.04  --sat_mode                              false
% 0.73/1.04  --sat_fm_restart_options                ""
% 0.73/1.04  --sat_gr_def                            false
% 0.73/1.04  --sat_epr_types                         true
% 0.73/1.04  --sat_non_cyclic_types                  false
% 0.73/1.04  --sat_finite_models                     false
% 0.73/1.04  --sat_fm_lemmas                         false
% 0.73/1.04  --sat_fm_prep                           false
% 0.73/1.04  --sat_fm_uc_incr                        true
% 0.73/1.04  --sat_out_model                         small
% 0.73/1.04  --sat_out_clauses                       false
% 0.73/1.04  
% 0.73/1.04  ------ QBF Options
% 0.73/1.04  
% 0.73/1.04  --qbf_mode                              false
% 0.73/1.04  --qbf_elim_univ                         false
% 0.73/1.04  --qbf_dom_inst                          none
% 0.73/1.04  --qbf_dom_pre_inst                      false
% 0.73/1.04  --qbf_sk_in                             false
% 0.73/1.04  --qbf_pred_elim                         true
% 0.73/1.04  --qbf_split                             512
% 0.73/1.04  
% 0.73/1.04  ------ BMC1 Options
% 0.73/1.04  
% 0.73/1.04  --bmc1_incremental                      false
% 0.73/1.04  --bmc1_axioms                           reachable_all
% 0.73/1.04  --bmc1_min_bound                        0
% 0.73/1.04  --bmc1_max_bound                        -1
% 0.73/1.04  --bmc1_max_bound_default                -1
% 0.73/1.04  --bmc1_symbol_reachability              true
% 0.73/1.04  --bmc1_property_lemmas                  false
% 0.73/1.04  --bmc1_k_induction                      false
% 0.73/1.04  --bmc1_non_equiv_states                 false
% 0.73/1.04  --bmc1_deadlock                         false
% 0.73/1.04  --bmc1_ucm                              false
% 0.73/1.04  --bmc1_add_unsat_core                   none
% 0.73/1.04  --bmc1_unsat_core_children              false
% 0.73/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.73/1.04  --bmc1_out_stat                         full
% 0.73/1.04  --bmc1_ground_init                      false
% 0.73/1.04  --bmc1_pre_inst_next_state              false
% 0.73/1.04  --bmc1_pre_inst_state                   false
% 0.73/1.04  --bmc1_pre_inst_reach_state             false
% 0.73/1.04  --bmc1_out_unsat_core                   false
% 0.73/1.04  --bmc1_aig_witness_out                  false
% 0.73/1.04  --bmc1_verbose                          false
% 0.73/1.04  --bmc1_dump_clauses_tptp                false
% 0.73/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.73/1.04  --bmc1_dump_file                        -
% 0.73/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.73/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.73/1.04  --bmc1_ucm_extend_mode                  1
% 0.73/1.04  --bmc1_ucm_init_mode                    2
% 0.73/1.04  --bmc1_ucm_cone_mode                    none
% 0.73/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.73/1.04  --bmc1_ucm_relax_model                  4
% 0.73/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.73/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.73/1.04  --bmc1_ucm_layered_model                none
% 0.73/1.04  --bmc1_ucm_max_lemma_size               10
% 0.73/1.04  
% 0.73/1.04  ------ AIG Options
% 0.73/1.04  
% 0.73/1.04  --aig_mode                              false
% 0.73/1.04  
% 0.73/1.04  ------ Instantiation Options
% 0.73/1.04  
% 0.73/1.04  --instantiation_flag                    true
% 0.73/1.04  --inst_sos_flag                         false
% 0.73/1.04  --inst_sos_phase                        true
% 0.73/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.73/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.73/1.04  --inst_lit_sel_side                     num_symb
% 0.73/1.04  --inst_solver_per_active                1400
% 0.73/1.04  --inst_solver_calls_frac                1.
% 0.73/1.04  --inst_passive_queue_type               priority_queues
% 0.73/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.73/1.04  --inst_passive_queues_freq              [25;2]
% 0.73/1.04  --inst_dismatching                      true
% 0.73/1.04  --inst_eager_unprocessed_to_passive     true
% 0.73/1.04  --inst_prop_sim_given                   true
% 0.73/1.04  --inst_prop_sim_new                     false
% 0.73/1.04  --inst_subs_new                         false
% 0.73/1.04  --inst_eq_res_simp                      false
% 0.73/1.04  --inst_subs_given                       false
% 0.73/1.04  --inst_orphan_elimination               true
% 0.73/1.04  --inst_learning_loop_flag               true
% 0.73/1.04  --inst_learning_start                   3000
% 0.73/1.04  --inst_learning_factor                  2
% 0.73/1.04  --inst_start_prop_sim_after_learn       3
% 0.73/1.04  --inst_sel_renew                        solver
% 0.73/1.04  --inst_lit_activity_flag                true
% 0.73/1.04  --inst_restr_to_given                   false
% 0.73/1.04  --inst_activity_threshold               500
% 0.73/1.04  --inst_out_proof                        true
% 0.73/1.04  
% 0.73/1.04  ------ Resolution Options
% 0.73/1.04  
% 0.73/1.04  --resolution_flag                       true
% 0.73/1.04  --res_lit_sel                           adaptive
% 0.73/1.04  --res_lit_sel_side                      none
% 0.73/1.04  --res_ordering                          kbo
% 0.73/1.04  --res_to_prop_solver                    active
% 0.73/1.04  --res_prop_simpl_new                    false
% 0.73/1.04  --res_prop_simpl_given                  true
% 0.73/1.04  --res_passive_queue_type                priority_queues
% 0.73/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.73/1.04  --res_passive_queues_freq               [15;5]
% 0.73/1.04  --res_forward_subs                      full
% 0.73/1.04  --res_backward_subs                     full
% 0.73/1.04  --res_forward_subs_resolution           true
% 0.73/1.04  --res_backward_subs_resolution          true
% 0.73/1.04  --res_orphan_elimination                true
% 0.73/1.04  --res_time_limit                        2.
% 0.73/1.04  --res_out_proof                         true
% 0.73/1.04  
% 0.73/1.04  ------ Superposition Options
% 0.73/1.04  
% 0.73/1.04  --superposition_flag                    true
% 0.73/1.04  --sup_passive_queue_type                priority_queues
% 0.73/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.73/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.73/1.04  --demod_completeness_check              fast
% 0.73/1.04  --demod_use_ground                      true
% 0.73/1.04  --sup_to_prop_solver                    passive
% 0.73/1.04  --sup_prop_simpl_new                    true
% 0.73/1.04  --sup_prop_simpl_given                  true
% 0.73/1.04  --sup_fun_splitting                     false
% 0.73/1.04  --sup_smt_interval                      50000
% 0.73/1.04  
% 0.73/1.04  ------ Superposition Simplification Setup
% 0.73/1.04  
% 0.73/1.04  --sup_indices_passive                   []
% 0.73/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.73/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.04  --sup_full_bw                           [BwDemod]
% 0.73/1.04  --sup_immed_triv                        [TrivRules]
% 0.73/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.04  --sup_immed_bw_main                     []
% 0.73/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.73/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.04  
% 0.73/1.04  ------ Combination Options
% 0.73/1.04  
% 0.73/1.04  --comb_res_mult                         3
% 0.73/1.04  --comb_sup_mult                         2
% 0.73/1.04  --comb_inst_mult                        10
% 0.73/1.04  
% 0.73/1.04  ------ Debug Options
% 0.73/1.04  
% 0.73/1.04  --dbg_backtrace                         false
% 0.73/1.04  --dbg_dump_prop_clauses                 false
% 0.73/1.04  --dbg_dump_prop_clauses_file            -
% 0.73/1.04  --dbg_out_stat                          false
% 0.73/1.04  ------ Parsing...
% 0.73/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.73/1.04  
% 0.73/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.73/1.04  
% 0.73/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.73/1.04  
% 0.73/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.73/1.04  ------ Proving...
% 0.73/1.04  ------ Problem Properties 
% 0.73/1.04  
% 0.73/1.04  
% 0.73/1.04  clauses                                 7
% 0.73/1.04  conjectures                             1
% 0.73/1.04  EPR                                     0
% 0.73/1.04  Horn                                    7
% 0.73/1.04  unary                                   5
% 0.73/1.04  binary                                  2
% 0.73/1.04  lits                                    9
% 0.73/1.04  lits eq                                 3
% 0.73/1.04  fd_pure                                 0
% 0.73/1.04  fd_pseudo                               0
% 0.73/1.04  fd_cond                                 0
% 0.73/1.04  fd_pseudo_cond                          0
% 0.73/1.04  AC symbols                              0
% 0.73/1.04  
% 0.73/1.04  ------ Schedule dynamic 5 is on 
% 0.73/1.04  
% 0.73/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.73/1.04  
% 0.73/1.04  
% 0.73/1.04  ------ 
% 0.73/1.04  Current options:
% 0.73/1.04  ------ 
% 0.73/1.04  
% 0.73/1.04  ------ Input Options
% 0.73/1.04  
% 0.73/1.04  --out_options                           all
% 0.73/1.04  --tptp_safe_out                         true
% 0.73/1.04  --problem_path                          ""
% 0.73/1.04  --include_path                          ""
% 0.73/1.04  --clausifier                            res/vclausify_rel
% 0.73/1.04  --clausifier_options                    --mode clausify
% 0.73/1.04  --stdin                                 false
% 0.73/1.04  --stats_out                             all
% 0.73/1.04  
% 0.73/1.04  ------ General Options
% 0.73/1.04  
% 0.73/1.04  --fof                                   false
% 0.73/1.04  --time_out_real                         305.
% 0.73/1.04  --time_out_virtual                      -1.
% 0.73/1.04  --symbol_type_check                     false
% 0.73/1.04  --clausify_out                          false
% 0.73/1.04  --sig_cnt_out                           false
% 0.73/1.04  --trig_cnt_out                          false
% 0.73/1.04  --trig_cnt_out_tolerance                1.
% 0.73/1.04  --trig_cnt_out_sk_spl                   false
% 0.73/1.04  --abstr_cl_out                          false
% 0.73/1.04  
% 0.73/1.04  ------ Global Options
% 0.73/1.04  
% 0.73/1.04  --schedule                              default
% 0.73/1.04  --add_important_lit                     false
% 0.73/1.04  --prop_solver_per_cl                    1000
% 0.73/1.04  --min_unsat_core                        false
% 0.73/1.04  --soft_assumptions                      false
% 0.73/1.04  --soft_lemma_size                       3
% 0.73/1.04  --prop_impl_unit_size                   0
% 0.73/1.04  --prop_impl_unit                        []
% 0.73/1.04  --share_sel_clauses                     true
% 0.73/1.04  --reset_solvers                         false
% 0.73/1.04  --bc_imp_inh                            [conj_cone]
% 0.73/1.04  --conj_cone_tolerance                   3.
% 0.73/1.04  --extra_neg_conj                        none
% 0.73/1.04  --large_theory_mode                     true
% 0.73/1.04  --prolific_symb_bound                   200
% 0.73/1.04  --lt_threshold                          2000
% 0.73/1.04  --clause_weak_htbl                      true
% 0.73/1.04  --gc_record_bc_elim                     false
% 0.73/1.04  
% 0.73/1.04  ------ Preprocessing Options
% 0.73/1.04  
% 0.73/1.04  --preprocessing_flag                    true
% 0.73/1.04  --time_out_prep_mult                    0.1
% 0.73/1.04  --splitting_mode                        input
% 0.73/1.04  --splitting_grd                         true
% 0.73/1.04  --splitting_cvd                         false
% 0.73/1.04  --splitting_cvd_svl                     false
% 0.73/1.04  --splitting_nvd                         32
% 0.73/1.04  --sub_typing                            true
% 0.73/1.04  --prep_gs_sim                           true
% 0.73/1.04  --prep_unflatten                        true
% 0.73/1.04  --prep_res_sim                          true
% 0.73/1.04  --prep_upred                            true
% 0.73/1.04  --prep_sem_filter                       exhaustive
% 0.73/1.04  --prep_sem_filter_out                   false
% 0.73/1.04  --pred_elim                             true
% 0.73/1.04  --res_sim_input                         true
% 0.73/1.04  --eq_ax_congr_red                       true
% 0.73/1.04  --pure_diseq_elim                       true
% 0.73/1.04  --brand_transform                       false
% 0.73/1.04  --non_eq_to_eq                          false
% 0.73/1.04  --prep_def_merge                        true
% 0.73/1.04  --prep_def_merge_prop_impl              false
% 0.73/1.04  --prep_def_merge_mbd                    true
% 0.73/1.04  --prep_def_merge_tr_red                 false
% 0.73/1.04  --prep_def_merge_tr_cl                  false
% 0.73/1.04  --smt_preprocessing                     true
% 0.73/1.04  --smt_ac_axioms                         fast
% 0.73/1.04  --preprocessed_out                      false
% 0.73/1.04  --preprocessed_stats                    false
% 0.73/1.04  
% 0.73/1.04  ------ Abstraction refinement Options
% 0.73/1.04  
% 0.73/1.04  --abstr_ref                             []
% 0.73/1.04  --abstr_ref_prep                        false
% 0.73/1.04  --abstr_ref_until_sat                   false
% 0.73/1.04  --abstr_ref_sig_restrict                funpre
% 0.73/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.73/1.04  --abstr_ref_under                       []
% 0.73/1.04  
% 0.73/1.04  ------ SAT Options
% 0.73/1.04  
% 0.73/1.04  --sat_mode                              false
% 0.73/1.04  --sat_fm_restart_options                ""
% 0.73/1.04  --sat_gr_def                            false
% 0.73/1.04  --sat_epr_types                         true
% 0.73/1.04  --sat_non_cyclic_types                  false
% 0.73/1.04  --sat_finite_models                     false
% 0.73/1.04  --sat_fm_lemmas                         false
% 0.73/1.04  --sat_fm_prep                           false
% 0.73/1.04  --sat_fm_uc_incr                        true
% 0.73/1.04  --sat_out_model                         small
% 0.73/1.04  --sat_out_clauses                       false
% 0.73/1.04  
% 0.73/1.04  ------ QBF Options
% 0.73/1.04  
% 0.73/1.04  --qbf_mode                              false
% 0.73/1.04  --qbf_elim_univ                         false
% 0.73/1.04  --qbf_dom_inst                          none
% 0.73/1.04  --qbf_dom_pre_inst                      false
% 0.73/1.04  --qbf_sk_in                             false
% 0.73/1.04  --qbf_pred_elim                         true
% 0.73/1.04  --qbf_split                             512
% 0.73/1.04  
% 0.73/1.04  ------ BMC1 Options
% 0.73/1.04  
% 0.73/1.04  --bmc1_incremental                      false
% 0.73/1.04  --bmc1_axioms                           reachable_all
% 0.73/1.04  --bmc1_min_bound                        0
% 0.73/1.04  --bmc1_max_bound                        -1
% 0.73/1.04  --bmc1_max_bound_default                -1
% 0.73/1.04  --bmc1_symbol_reachability              true
% 0.73/1.04  --bmc1_property_lemmas                  false
% 0.73/1.04  --bmc1_k_induction                      false
% 0.73/1.04  --bmc1_non_equiv_states                 false
% 0.73/1.04  --bmc1_deadlock                         false
% 0.73/1.04  --bmc1_ucm                              false
% 0.73/1.04  --bmc1_add_unsat_core                   none
% 0.73/1.04  --bmc1_unsat_core_children              false
% 0.73/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.73/1.04  --bmc1_out_stat                         full
% 0.73/1.04  --bmc1_ground_init                      false
% 0.73/1.04  --bmc1_pre_inst_next_state              false
% 0.73/1.04  --bmc1_pre_inst_state                   false
% 0.73/1.04  --bmc1_pre_inst_reach_state             false
% 0.73/1.04  --bmc1_out_unsat_core                   false
% 0.73/1.04  --bmc1_aig_witness_out                  false
% 0.73/1.04  --bmc1_verbose                          false
% 0.73/1.04  --bmc1_dump_clauses_tptp                false
% 0.73/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.73/1.04  --bmc1_dump_file                        -
% 0.73/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.73/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.73/1.04  --bmc1_ucm_extend_mode                  1
% 0.73/1.04  --bmc1_ucm_init_mode                    2
% 0.73/1.04  --bmc1_ucm_cone_mode                    none
% 0.73/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.73/1.04  --bmc1_ucm_relax_model                  4
% 0.73/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.73/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.73/1.04  --bmc1_ucm_layered_model                none
% 0.73/1.04  --bmc1_ucm_max_lemma_size               10
% 0.73/1.04  
% 0.73/1.04  ------ AIG Options
% 0.73/1.04  
% 0.73/1.04  --aig_mode                              false
% 0.73/1.04  
% 0.73/1.04  ------ Instantiation Options
% 0.73/1.04  
% 0.73/1.04  --instantiation_flag                    true
% 0.73/1.04  --inst_sos_flag                         false
% 0.73/1.04  --inst_sos_phase                        true
% 0.73/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.73/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.73/1.04  --inst_lit_sel_side                     none
% 0.73/1.04  --inst_solver_per_active                1400
% 0.73/1.04  --inst_solver_calls_frac                1.
% 0.73/1.04  --inst_passive_queue_type               priority_queues
% 0.73/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.73/1.04  --inst_passive_queues_freq              [25;2]
% 0.73/1.04  --inst_dismatching                      true
% 0.73/1.04  --inst_eager_unprocessed_to_passive     true
% 0.73/1.04  --inst_prop_sim_given                   true
% 0.73/1.04  --inst_prop_sim_new                     false
% 0.73/1.04  --inst_subs_new                         false
% 0.73/1.04  --inst_eq_res_simp                      false
% 0.73/1.04  --inst_subs_given                       false
% 0.73/1.04  --inst_orphan_elimination               true
% 0.73/1.04  --inst_learning_loop_flag               true
% 0.73/1.04  --inst_learning_start                   3000
% 0.73/1.04  --inst_learning_factor                  2
% 0.73/1.04  --inst_start_prop_sim_after_learn       3
% 0.73/1.04  --inst_sel_renew                        solver
% 0.73/1.04  --inst_lit_activity_flag                true
% 0.73/1.04  --inst_restr_to_given                   false
% 0.73/1.04  --inst_activity_threshold               500
% 0.73/1.04  --inst_out_proof                        true
% 0.73/1.04  
% 0.73/1.04  ------ Resolution Options
% 0.73/1.04  
% 0.73/1.04  --resolution_flag                       false
% 0.73/1.04  --res_lit_sel                           adaptive
% 0.73/1.04  --res_lit_sel_side                      none
% 0.73/1.04  --res_ordering                          kbo
% 0.73/1.04  --res_to_prop_solver                    active
% 0.73/1.04  --res_prop_simpl_new                    false
% 0.73/1.04  --res_prop_simpl_given                  true
% 0.73/1.04  --res_passive_queue_type                priority_queues
% 0.73/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.73/1.04  --res_passive_queues_freq               [15;5]
% 0.73/1.04  --res_forward_subs                      full
% 0.73/1.04  --res_backward_subs                     full
% 0.73/1.04  --res_forward_subs_resolution           true
% 0.73/1.04  --res_backward_subs_resolution          true
% 0.73/1.04  --res_orphan_elimination                true
% 0.73/1.04  --res_time_limit                        2.
% 0.73/1.04  --res_out_proof                         true
% 0.73/1.04  
% 0.73/1.04  ------ Superposition Options
% 0.73/1.04  
% 0.73/1.04  --superposition_flag                    true
% 0.73/1.04  --sup_passive_queue_type                priority_queues
% 0.73/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.73/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.73/1.04  --demod_completeness_check              fast
% 0.73/1.04  --demod_use_ground                      true
% 0.73/1.04  --sup_to_prop_solver                    passive
% 0.73/1.04  --sup_prop_simpl_new                    true
% 0.73/1.04  --sup_prop_simpl_given                  true
% 0.73/1.04  --sup_fun_splitting                     false
% 0.73/1.04  --sup_smt_interval                      50000
% 0.73/1.04  
% 0.73/1.04  ------ Superposition Simplification Setup
% 0.73/1.04  
% 0.73/1.04  --sup_indices_passive                   []
% 0.73/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.73/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.04  --sup_full_bw                           [BwDemod]
% 0.73/1.04  --sup_immed_triv                        [TrivRules]
% 0.73/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.04  --sup_immed_bw_main                     []
% 0.73/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.73/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.04  
% 0.73/1.04  ------ Combination Options
% 0.73/1.04  
% 0.73/1.04  --comb_res_mult                         3
% 0.73/1.04  --comb_sup_mult                         2
% 0.73/1.04  --comb_inst_mult                        10
% 0.73/1.04  
% 0.73/1.04  ------ Debug Options
% 0.73/1.04  
% 0.73/1.04  --dbg_backtrace                         false
% 0.73/1.04  --dbg_dump_prop_clauses                 false
% 0.73/1.04  --dbg_dump_prop_clauses_file            -
% 0.73/1.04  --dbg_out_stat                          false
% 0.73/1.04  
% 0.73/1.04  
% 0.73/1.04  
% 0.73/1.04  
% 0.73/1.04  ------ Proving...
% 0.73/1.04  
% 0.73/1.04  
% 0.73/1.04  % SZS status Theorem for theBenchmark.p
% 0.73/1.04  
% 0.73/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.73/1.04  
% 0.73/1.04  fof(f5,axiom,(
% 0.73/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f16,plain,(
% 0.73/1.04    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.73/1.04    inference(ennf_transformation,[],[f5])).
% 0.73/1.04  
% 0.73/1.04  fof(f25,plain,(
% 0.73/1.04    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.73/1.04    inference(nnf_transformation,[],[f16])).
% 0.73/1.04  
% 0.73/1.04  fof(f37,plain,(
% 0.73/1.04    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.73/1.04    inference(cnf_transformation,[],[f25])).
% 0.73/1.04  
% 0.73/1.04  fof(f6,axiom,(
% 0.73/1.04    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f17,plain,(
% 0.73/1.04    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.73/1.04    inference(ennf_transformation,[],[f6])).
% 0.73/1.04  
% 0.73/1.04  fof(f26,plain,(
% 0.73/1.04    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.73/1.04    introduced(choice_axiom,[])).
% 0.73/1.04  
% 0.73/1.04  fof(f27,plain,(
% 0.73/1.04    ! [X0] : ((v1_tops_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.73/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).
% 0.73/1.04  
% 0.73/1.04  fof(f40,plain,(
% 0.73/1.04    ( ! [X0] : (v1_tops_1(sK0(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.73/1.04    inference(cnf_transformation,[],[f27])).
% 0.73/1.04  
% 0.73/1.04  fof(f39,plain,(
% 0.73/1.04    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.73/1.04    inference(cnf_transformation,[],[f27])).
% 0.73/1.04  
% 0.73/1.04  fof(f9,conjecture,(
% 0.73/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f10,negated_conjecture,(
% 0.73/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.73/1.04    inference(negated_conjecture,[],[f9])).
% 0.73/1.04  
% 0.73/1.04  fof(f11,plain,(
% 0.73/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.73/1.04    inference(pure_predicate_removal,[],[f10])).
% 0.73/1.04  
% 0.73/1.04  fof(f22,plain,(
% 0.73/1.04    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.73/1.04    inference(ennf_transformation,[],[f11])).
% 0.73/1.04  
% 0.73/1.04  fof(f23,plain,(
% 0.73/1.04    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.73/1.04    inference(flattening,[],[f22])).
% 0.73/1.04  
% 0.73/1.04  fof(f30,plain,(
% 0.73/1.04    ( ! [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~m2_connsp_2(k2_struct_0(X0),X0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.73/1.04    introduced(choice_axiom,[])).
% 0.73/1.04  
% 0.73/1.04  fof(f29,plain,(
% 0.73/1.04    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK1),sK1,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.73/1.04    introduced(choice_axiom,[])).
% 0.73/1.04  
% 0.73/1.04  fof(f31,plain,(
% 0.73/1.04    (~m2_connsp_2(k2_struct_0(sK1),sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 0.73/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f30,f29])).
% 0.73/1.04  
% 0.73/1.04  fof(f45,plain,(
% 0.73/1.04    l1_pre_topc(sK1)),
% 0.73/1.04    inference(cnf_transformation,[],[f31])).
% 0.73/1.04  
% 0.73/1.04  fof(f3,axiom,(
% 0.73/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f13,plain,(
% 0.73/1.04    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.73/1.04    inference(ennf_transformation,[],[f3])).
% 0.73/1.04  
% 0.73/1.04  fof(f14,plain,(
% 0.73/1.04    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.73/1.04    inference(flattening,[],[f13])).
% 0.73/1.04  
% 0.73/1.04  fof(f35,plain,(
% 0.73/1.04    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.73/1.04    inference(cnf_transformation,[],[f14])).
% 0.73/1.04  
% 0.73/1.04  fof(f4,axiom,(
% 0.73/1.04    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f15,plain,(
% 0.73/1.04    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.73/1.04    inference(ennf_transformation,[],[f4])).
% 0.73/1.04  
% 0.73/1.04  fof(f36,plain,(
% 0.73/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.73/1.04    inference(cnf_transformation,[],[f15])).
% 0.73/1.04  
% 0.73/1.04  fof(f2,axiom,(
% 0.73/1.04    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f12,plain,(
% 0.73/1.04    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.73/1.04    inference(ennf_transformation,[],[f2])).
% 0.73/1.04  
% 0.73/1.04  fof(f34,plain,(
% 0.73/1.04    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.73/1.04    inference(cnf_transformation,[],[f12])).
% 0.73/1.04  
% 0.73/1.04  fof(f1,axiom,(
% 0.73/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f24,plain,(
% 0.73/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.73/1.04    inference(nnf_transformation,[],[f1])).
% 0.73/1.04  
% 0.73/1.04  fof(f32,plain,(
% 0.73/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.73/1.04    inference(cnf_transformation,[],[f24])).
% 0.73/1.04  
% 0.73/1.04  fof(f47,plain,(
% 0.73/1.04    ~m2_connsp_2(k2_struct_0(sK1),sK1,sK2)),
% 0.73/1.04    inference(cnf_transformation,[],[f31])).
% 0.73/1.04  
% 0.73/1.04  fof(f8,axiom,(
% 0.73/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f20,plain,(
% 0.73/1.04    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.73/1.04    inference(ennf_transformation,[],[f8])).
% 0.73/1.04  
% 0.73/1.04  fof(f21,plain,(
% 0.73/1.04    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.73/1.04    inference(flattening,[],[f20])).
% 0.73/1.04  
% 0.73/1.04  fof(f28,plain,(
% 0.73/1.04    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.73/1.04    inference(nnf_transformation,[],[f21])).
% 0.73/1.04  
% 0.73/1.04  fof(f43,plain,(
% 0.73/1.04    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.73/1.04    inference(cnf_transformation,[],[f28])).
% 0.73/1.04  
% 0.73/1.04  fof(f44,plain,(
% 0.73/1.04    v2_pre_topc(sK1)),
% 0.73/1.04    inference(cnf_transformation,[],[f31])).
% 0.73/1.04  
% 0.73/1.04  fof(f46,plain,(
% 0.73/1.04    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.73/1.04    inference(cnf_transformation,[],[f31])).
% 0.73/1.04  
% 0.73/1.04  fof(f7,axiom,(
% 0.73/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.73/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.04  
% 0.73/1.04  fof(f18,plain,(
% 0.73/1.04    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.73/1.04    inference(ennf_transformation,[],[f7])).
% 0.73/1.04  
% 0.73/1.04  fof(f19,plain,(
% 0.73/1.04    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.73/1.04    inference(flattening,[],[f18])).
% 0.73/1.04  
% 0.73/1.04  fof(f41,plain,(
% 0.73/1.04    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.73/1.04    inference(cnf_transformation,[],[f19])).
% 0.73/1.04  
% 0.73/1.04  cnf(c_6,plain,
% 0.73/1.04      ( ~ v1_tops_1(X0,X1)
% 0.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | ~ l1_pre_topc(X1)
% 0.73/1.04      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 0.73/1.04      inference(cnf_transformation,[],[f37]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_7,plain,
% 0.73/1.04      ( v1_tops_1(sK0(X0),X0) | ~ l1_pre_topc(X0) ),
% 0.73/1.04      inference(cnf_transformation,[],[f40]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_237,plain,
% 0.73/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | ~ l1_pre_topc(X1)
% 0.73/1.04      | ~ l1_pre_topc(X2)
% 0.73/1.04      | X2 != X1
% 0.73/1.04      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 0.73/1.04      | sK0(X2) != X0 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_238,plain,
% 0.73/1.04      ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 0.73/1.04      | ~ l1_pre_topc(X0)
% 0.73/1.04      | k2_pre_topc(X0,sK0(X0)) = k2_struct_0(X0) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_237]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_8,plain,
% 0.73/1.04      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 0.73/1.04      | ~ l1_pre_topc(X0) ),
% 0.73/1.04      inference(cnf_transformation,[],[f39]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_242,plain,
% 0.73/1.04      ( ~ l1_pre_topc(X0) | k2_pre_topc(X0,sK0(X0)) = k2_struct_0(X0) ),
% 0.73/1.04      inference(global_propositional_subsumption,
% 0.73/1.04                [status(thm)],
% 0.73/1.04                [c_238,c_8]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_14,negated_conjecture,
% 0.73/1.04      ( l1_pre_topc(sK1) ),
% 0.73/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_325,plain,
% 0.73/1.04      ( k2_pre_topc(X0,sK0(X0)) = k2_struct_0(X0) | sK1 != X0 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_242,c_14]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_326,plain,
% 0.73/1.04      ( k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_325]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_433,plain,
% 0.73/1.04      ( k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1) ),
% 0.73/1.04      inference(subtyping,[status(esa)],[c_326]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_3,plain,
% 0.73/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | ~ l1_pre_topc(X1) ),
% 0.73/1.04      inference(cnf_transformation,[],[f35]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_342,plain,
% 0.73/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | sK1 != X1 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_343,plain,
% 0.73/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_342]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_430,plain,
% 0.73/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | m1_subset_1(k2_pre_topc(sK1,X0_43),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(subtyping,[status(esa)],[c_343]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_528,plain,
% 0.73/1.04      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.73/1.04      | m1_subset_1(k2_pre_topc(sK1,X0_43),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.73/1.04      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_4,plain,
% 0.73/1.04      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 0.73/1.04      inference(cnf_transformation,[],[f36]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_2,plain,
% 0.73/1.04      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.73/1.04      inference(cnf_transformation,[],[f34]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_222,plain,
% 0.73/1.04      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.73/1.04      inference(resolution,[status(thm)],[c_4,c_2]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_330,plain,
% 0.73/1.04      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_222,c_14]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_331,plain,
% 0.73/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_330]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_432,plain,
% 0.73/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.73/1.04      inference(subtyping,[status(esa)],[c_331]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_542,plain,
% 0.73/1.04      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 0.73/1.04      | m1_subset_1(k2_pre_topc(sK1,X0_43),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 0.73/1.04      inference(light_normalisation,[status(thm)],[c_528,c_432]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_659,plain,
% 0.73/1.04      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 0.73/1.04      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 0.73/1.04      inference(superposition,[status(thm)],[c_433,c_542]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_1,plain,
% 0.73/1.04      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.73/1.04      inference(cnf_transformation,[],[f32]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_126,plain,
% 0.73/1.04      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.73/1.04      inference(prop_impl,[status(thm)],[c_1]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_12,negated_conjecture,
% 0.73/1.04      ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
% 0.73/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_10,plain,
% 0.73/1.04      ( m2_connsp_2(X0,X1,X2)
% 0.73/1.04      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 0.73/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | ~ v2_pre_topc(X1)
% 0.73/1.04      | ~ l1_pre_topc(X1) ),
% 0.73/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_15,negated_conjecture,
% 0.73/1.04      ( v2_pre_topc(sK1) ),
% 0.73/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_290,plain,
% 0.73/1.04      ( m2_connsp_2(X0,X1,X2)
% 0.73/1.04      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 0.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.04      | ~ l1_pre_topc(X1)
% 0.73/1.04      | sK1 != X1 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_291,plain,
% 0.73/1.04      ( m2_connsp_2(X0,sK1,X1)
% 0.73/1.04      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 0.73/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ l1_pre_topc(sK1) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_290]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_295,plain,
% 0.73/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 0.73/1.04      | m2_connsp_2(X0,sK1,X1) ),
% 0.73/1.04      inference(global_propositional_subsumption,
% 0.73/1.04                [status(thm)],
% 0.73/1.04                [c_291,c_14]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_296,plain,
% 0.73/1.04      ( m2_connsp_2(X0,sK1,X1)
% 0.73/1.04      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 0.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(renaming,[status(thm)],[c_295]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_362,plain,
% 0.73/1.04      ( ~ r1_tarski(X0,k1_tops_1(sK1,X1))
% 0.73/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | k2_struct_0(sK1) != X1
% 0.73/1.04      | sK2 != X0
% 0.73/1.04      | sK1 != sK1 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_296]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_363,plain,
% 0.73/1.04      ( ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_362]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_13,negated_conjecture,
% 0.73/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_365,plain,
% 0.73/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
% 0.73/1.04      inference(global_propositional_subsumption,
% 0.73/1.04                [status(thm)],
% 0.73/1.04                [c_363,c_13]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_366,plain,
% 0.73/1.04      ( ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(renaming,[status(thm)],[c_365]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_380,plain,
% 0.73/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.73/1.04      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | k1_tops_1(sK1,k2_struct_0(sK1)) != X1
% 0.73/1.04      | sK2 != X0 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_126,c_366]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_381,plain,
% 0.73/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK1,k2_struct_0(sK1)))) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_380]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_429,plain,
% 0.73/1.04      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.73/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK1,k2_struct_0(sK1)))) ),
% 0.73/1.04      inference(subtyping,[status(esa)],[c_381]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_529,plain,
% 0.73/1.04      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.73/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK1,k2_struct_0(sK1)))) != iProver_top ),
% 0.73/1.04      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_9,plain,
% 0.73/1.04      ( ~ v2_pre_topc(X0)
% 0.73/1.04      | ~ l1_pre_topc(X0)
% 0.73/1.04      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 0.73/1.04      inference(cnf_transformation,[],[f41]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_258,plain,
% 0.73/1.04      ( ~ l1_pre_topc(X0)
% 0.73/1.04      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 0.73/1.04      | sK1 != X0 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_259,plain,
% 0.73/1.04      ( ~ l1_pre_topc(sK1)
% 0.73/1.04      | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_258]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_27,plain,
% 0.73/1.04      ( ~ v2_pre_topc(sK1)
% 0.73/1.04      | ~ l1_pre_topc(sK1)
% 0.73/1.04      | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 0.73/1.04      inference(instantiation,[status(thm)],[c_9]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_261,plain,
% 0.73/1.04      ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 0.73/1.04      inference(global_propositional_subsumption,
% 0.73/1.04                [status(thm)],
% 0.73/1.04                [c_259,c_15,c_14,c_27]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_434,plain,
% 0.73/1.04      ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 0.73/1.04      inference(subtyping,[status(esa)],[c_261]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_547,plain,
% 0.73/1.04      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 0.73/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 0.73/1.04      inference(light_normalisation,[status(thm)],[c_529,c_432,c_434]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_435,negated_conjecture,
% 0.73/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(subtyping,[status(esa)],[c_13]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_526,plain,
% 0.73/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.73/1.04      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_532,plain,
% 0.73/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 0.73/1.04      inference(light_normalisation,[status(thm)],[c_526,c_432]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_550,plain,
% 0.73/1.04      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 0.73/1.04      inference(forward_subsumption_resolution,
% 0.73/1.04                [status(thm)],
% 0.73/1.04                [c_547,c_532]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_335,plain,
% 0.73/1.04      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK1 != X0 ),
% 0.73/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_336,plain,
% 0.73/1.04      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(unflattening,[status(thm)],[c_335]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_431,plain,
% 0.73/1.04      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.73/1.04      inference(subtyping,[status(esa)],[c_336]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_527,plain,
% 0.73/1.04      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.73/1.04      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(c_539,plain,
% 0.73/1.04      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 0.73/1.04      inference(light_normalisation,[status(thm)],[c_527,c_432]) ).
% 0.73/1.04  
% 0.73/1.04  cnf(contradiction,plain,
% 0.73/1.04      ( $false ),
% 0.73/1.04      inference(minisat,[status(thm)],[c_659,c_550,c_539]) ).
% 0.73/1.04  
% 0.73/1.04  
% 0.73/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.73/1.04  
% 0.73/1.04  ------                               Statistics
% 0.73/1.04  
% 0.73/1.04  ------ General
% 0.73/1.04  
% 0.73/1.04  abstr_ref_over_cycles:                  0
% 0.73/1.04  abstr_ref_under_cycles:                 0
% 0.73/1.04  gc_basic_clause_elim:                   0
% 0.73/1.04  forced_gc_time:                         0
% 0.73/1.04  parsing_time:                           0.012
% 0.73/1.04  unif_index_cands_time:                  0.
% 0.73/1.04  unif_index_add_time:                    0.
% 0.73/1.04  orderings_time:                         0.
% 0.73/1.04  out_proof_time:                         0.013
% 0.73/1.04  total_time:                             0.061
% 0.73/1.04  num_of_symbols:                         46
% 0.73/1.04  num_of_terms:                           639
% 0.73/1.04  
% 0.73/1.04  ------ Preprocessing
% 0.73/1.04  
% 0.73/1.04  num_of_splits:                          0
% 0.73/1.04  num_of_split_atoms:                     0
% 0.73/1.04  num_of_reused_defs:                     0
% 0.73/1.04  num_eq_ax_congr_red:                    12
% 0.73/1.04  num_of_sem_filtered_clauses:            1
% 0.73/1.04  num_of_subtypes:                        3
% 0.73/1.04  monotx_restored_types:                  0
% 0.73/1.04  sat_num_of_epr_types:                   0
% 0.73/1.04  sat_num_of_non_cyclic_types:            0
% 0.73/1.04  sat_guarded_non_collapsed_types:        0
% 0.73/1.04  num_pure_diseq_elim:                    0
% 0.73/1.04  simp_replaced_by:                       0
% 0.73/1.04  res_preprocessed:                       52
% 0.73/1.04  prep_upred:                             0
% 0.73/1.04  prep_unflattend:                        13
% 0.73/1.04  smt_new_axioms:                         0
% 0.73/1.04  pred_elim_cands:                        1
% 0.73/1.04  pred_elim:                              6
% 0.73/1.04  pred_elim_cl:                           9
% 0.73/1.04  pred_elim_cycles:                       8
% 0.73/1.04  merged_defs:                            2
% 0.73/1.04  merged_defs_ncl:                        0
% 0.73/1.04  bin_hyper_res:                          2
% 0.73/1.04  prep_cycles:                            4
% 0.73/1.04  pred_elim_time:                         0.004
% 0.73/1.04  splitting_time:                         0.
% 0.73/1.04  sem_filter_time:                        0.
% 0.73/1.04  monotx_time:                            0.
% 0.73/1.04  subtype_inf_time:                       0.
% 0.73/1.04  
% 0.73/1.04  ------ Problem properties
% 0.73/1.04  
% 0.73/1.04  clauses:                                7
% 0.73/1.04  conjectures:                            1
% 0.73/1.04  epr:                                    0
% 0.73/1.04  horn:                                   7
% 0.73/1.04  ground:                                 6
% 0.73/1.04  unary:                                  5
% 0.73/1.04  binary:                                 2
% 0.73/1.04  lits:                                   9
% 0.73/1.04  lits_eq:                                3
% 0.73/1.04  fd_pure:                                0
% 0.73/1.04  fd_pseudo:                              0
% 0.73/1.04  fd_cond:                                0
% 0.73/1.04  fd_pseudo_cond:                         0
% 0.73/1.04  ac_symbols:                             0
% 0.73/1.04  
% 0.73/1.04  ------ Propositional Solver
% 0.73/1.04  
% 0.73/1.04  prop_solver_calls:                      24
% 0.73/1.04  prop_fast_solver_calls:                 247
% 0.73/1.04  smt_solver_calls:                       0
% 0.73/1.04  smt_fast_solver_calls:                  0
% 0.73/1.04  prop_num_of_clauses:                    183
% 0.73/1.04  prop_preprocess_simplified:             1124
% 0.73/1.04  prop_fo_subsumed:                       5
% 0.73/1.04  prop_solver_time:                       0.
% 0.73/1.04  smt_solver_time:                        0.
% 0.73/1.04  smt_fast_solver_time:                   0.
% 0.73/1.04  prop_fast_solver_time:                  0.
% 0.73/1.04  prop_unsat_core_time:                   0.
% 0.73/1.04  
% 0.73/1.04  ------ QBF
% 0.73/1.04  
% 0.73/1.04  qbf_q_res:                              0
% 0.73/1.04  qbf_num_tautologies:                    0
% 0.73/1.04  qbf_prep_cycles:                        0
% 0.73/1.04  
% 0.73/1.04  ------ BMC1
% 0.73/1.04  
% 0.73/1.04  bmc1_current_bound:                     -1
% 0.73/1.04  bmc1_last_solved_bound:                 -1
% 0.73/1.04  bmc1_unsat_core_size:                   -1
% 0.73/1.04  bmc1_unsat_core_parents_size:           -1
% 0.73/1.04  bmc1_merge_next_fun:                    0
% 0.73/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.73/1.04  
% 0.73/1.04  ------ Instantiation
% 0.73/1.04  
% 0.73/1.04  inst_num_of_clauses:                    33
% 0.73/1.04  inst_num_in_passive:                    5
% 0.73/1.04  inst_num_in_active:                     25
% 0.73/1.04  inst_num_in_unprocessed:                3
% 0.73/1.04  inst_num_of_loops:                      30
% 0.73/1.04  inst_num_of_learning_restarts:          0
% 0.73/1.04  inst_num_moves_active_passive:          3
% 0.73/1.04  inst_lit_activity:                      0
% 0.73/1.04  inst_lit_activity_moves:                0
% 0.73/1.04  inst_num_tautologies:                   0
% 0.73/1.04  inst_num_prop_implied:                  0
% 0.73/1.04  inst_num_existing_simplified:           0
% 0.73/1.04  inst_num_eq_res_simplified:             0
% 0.73/1.04  inst_num_child_elim:                    0
% 0.73/1.04  inst_num_of_dismatching_blockings:      0
% 0.73/1.04  inst_num_of_non_proper_insts:           15
% 0.73/1.04  inst_num_of_duplicates:                 0
% 0.73/1.04  inst_inst_num_from_inst_to_res:         0
% 0.73/1.04  inst_dismatching_checking_time:         0.
% 0.73/1.04  
% 0.73/1.04  ------ Resolution
% 0.73/1.04  
% 0.73/1.04  res_num_of_clauses:                     0
% 0.73/1.04  res_num_in_passive:                     0
% 0.73/1.04  res_num_in_active:                      0
% 0.73/1.04  res_num_of_loops:                       56
% 0.73/1.04  res_forward_subset_subsumed:            1
% 0.73/1.04  res_backward_subset_subsumed:           0
% 0.73/1.04  res_forward_subsumed:                   0
% 0.73/1.04  res_backward_subsumed:                  0
% 0.73/1.04  res_forward_subsumption_resolution:     0
% 0.73/1.04  res_backward_subsumption_resolution:    0
% 0.73/1.04  res_clause_to_clause_subsumption:       22
% 0.73/1.04  res_orphan_elimination:                 0
% 0.73/1.04  res_tautology_del:                      9
% 0.73/1.04  res_num_eq_res_simplified:              0
% 0.73/1.04  res_num_sel_changes:                    0
% 0.73/1.04  res_moves_from_active_to_pass:          0
% 0.73/1.04  
% 0.73/1.04  ------ Superposition
% 0.73/1.04  
% 0.73/1.04  sup_time_total:                         0.
% 0.73/1.04  sup_time_generating:                    0.
% 0.73/1.04  sup_time_sim_full:                      0.
% 0.73/1.04  sup_time_sim_immed:                     0.
% 0.73/1.04  
% 0.73/1.04  sup_num_of_clauses:                     8
% 0.73/1.04  sup_num_in_active:                      6
% 0.73/1.04  sup_num_in_passive:                     2
% 0.73/1.04  sup_num_of_loops:                       5
% 0.73/1.04  sup_fw_superposition:                   1
% 0.73/1.04  sup_bw_superposition:                   0
% 0.73/1.04  sup_immediate_simplified:               0
% 0.73/1.04  sup_given_eliminated:                   0
% 0.73/1.04  comparisons_done:                       0
% 0.73/1.04  comparisons_avoided:                    0
% 0.73/1.04  
% 0.73/1.04  ------ Simplifications
% 0.73/1.04  
% 0.73/1.04  
% 0.73/1.04  sim_fw_subset_subsumed:                 0
% 0.73/1.04  sim_bw_subset_subsumed:                 0
% 0.73/1.04  sim_fw_subsumed:                        0
% 0.73/1.04  sim_bw_subsumed:                        0
% 0.73/1.04  sim_fw_subsumption_res:                 1
% 0.73/1.04  sim_bw_subsumption_res:                 0
% 0.73/1.04  sim_tautology_del:                      0
% 0.73/1.04  sim_eq_tautology_del:                   0
% 0.73/1.04  sim_eq_res_simp:                        0
% 0.73/1.04  sim_fw_demodulated:                     0
% 0.73/1.04  sim_bw_demodulated:                     0
% 0.73/1.04  sim_light_normalised:                   4
% 0.73/1.04  sim_joinable_taut:                      0
% 0.73/1.04  sim_joinable_simp:                      0
% 0.73/1.04  sim_ac_normalised:                      0
% 0.73/1.04  sim_smt_subsumption:                    0
% 0.73/1.04  
%------------------------------------------------------------------------------
