%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2022+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:02 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   83 (1070 expanded)
%              Number of clauses        :   56 ( 226 expanded)
%              Number of leaves         :    7 ( 362 expanded)
%              Depth                    :   28
%              Number of atoms          :  392 (6061 expanded)
%              Number of equality atoms :   80 ( 290 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => m1_connsp_2(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_connsp_2(sK3,X0,X1)
        & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ m1_connsp_2(X2,X0,sK2)
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK2))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,sK1,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f15,f14,f13])).

fof(f26,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK0(X0,X1,X2),X0)
        & r2_hidden(X1,sK0(X0,X1,X2))
        & sK0(X0,X1,X2) = X2
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK0(X0,X1,X2),X0)
                & r2_hidden(X1,sK0(X0,X1,X2))
                & sK0(X0,X1,X2) = X2
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f11])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( sK0(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_352,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_494,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_8,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK0(X1,X0,X2) = X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | sK0(sK1,X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_10,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | sK0(sK1,X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_10,c_9])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(k9_yellow_6(sK1,X1_42)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | sK0(sK1,X1_42,X0_42) = X0_42 ),
    inference(subtyping,[status(esa)],[c_279])).

cnf(c_500,plain,
    ( sK0(sK1,X0_42,X1_42) = X1_42
    | m1_subset_1(X1_42,u1_struct_0(k9_yellow_6(sK1,X0_42))) != iProver_top
    | m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_598,plain,
    ( sK0(sK1,sK2,sK3) = sK3
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_500])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_555,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | sK0(sK1,sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_651,plain,
    ( sK0(sK1,sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_7,c_6,c_555])).

cnf(c_1,plain,
    ( r2_hidden(X0,sK0(X1,X0,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v3_pre_topc(sK0(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,negated_conjecture,
    ( ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_122,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | sK2 != X0
    | sK1 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_123,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_125,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_123,c_10,c_9,c_8,c_7])).

cnf(c_126,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(sK3,sK1) ),
    inference(renaming,[status(thm)],[c_125])).

cnf(c_143,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0,X2) != sK3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_126])).

cnf(c_144,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,X1,X0) != sK3 ),
    inference(unflattening,[status(thm)],[c_143])).

cnf(c_148,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ r2_hidden(sK2,sK3)
    | sK0(sK1,X1,X0) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_144,c_10,c_9,c_8])).

cnf(c_149,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,X1,X0) != sK3 ),
    inference(renaming,[status(thm)],[c_148])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK1,X4)))
    | ~ m1_subset_1(X4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0,X2) != sK3
    | sK0(sK1,X4,X3) != sK3
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_149])).

cnf(c_177,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(X1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,sK2,X0) != sK3
    | sK0(sK1,X3,X2) != sK3 ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(X1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK0(X1,sK2,X0) != sK3
    | sK0(sK1,X3,X2) != sK3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_177,c_8])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | sK0(sK1,X1,X0) != sK3
    | sK0(sK1,sK2,X2) != sK3 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,X1,X0) != sK3
    | sK0(sK1,sK2,X2) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_224,c_10,c_9,c_7])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,X1,X0) != sK3
    | sK0(sK1,sK2,X2) != sK3 ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(k9_yellow_6(sK1,X1_42)))
    | ~ m1_subset_1(X2_42,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,X1_42,X0_42) != sK3
    | sK0(sK1,sK2,X2_42) != sK3 ),
    inference(subtyping,[status(esa)],[c_229])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(k9_yellow_6(sK1,X1_42)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | sK0(sK1,X1_42,X0_42) != sK3
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_350])).

cnf(c_497,plain,
    ( sK0(sK1,X0_42,X1_42) != sK3
    | m1_subset_1(X1_42,u1_struct_0(k9_yellow_6(sK1,X0_42))) != iProver_top
    | m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_14,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_355,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_350])).

cnf(c_377,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_378,plain,
    ( sK0(sK1,X0_42,X1_42) != sK3
    | m1_subset_1(X1_42,u1_struct_0(k9_yellow_6(sK1,X0_42))) != iProver_top
    | m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(k9_yellow_6(sK1,sK2)))
    | sK0(sK1,sK2,X0_42) != sK3
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_350])).

cnf(c_498,plain,
    ( sK0(sK1,sK2,X0_42) != sK3
    | m1_subset_1(X0_42,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_654,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_651,c_498])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK1,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_10,c_9])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(k9_yellow_6(sK1,X1_42)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X1_42,X0_42),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_499,plain,
    ( m1_subset_1(X0_42,u1_struct_0(k9_yellow_6(sK1,X1_42))) != iProver_top
    | m1_subset_1(X1_42,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X1_42,X0_42),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_660,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_651,c_499])).

cnf(c_719,plain,
    ( m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_42,u1_struct_0(k9_yellow_6(sK1,X0_42))) != iProver_top
    | sK0(sK1,X0_42,X1_42) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_14,c_15,c_377,c_378,c_654,c_660])).

cnf(c_720,plain,
    ( sK0(sK1,X0_42,X1_42) != sK3
    | m1_subset_1(X1_42,u1_struct_0(k9_yellow_6(sK1,X0_42))) != iProver_top
    | m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_719])).

cnf(c_728,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_651,c_720])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_728,c_15,c_14])).


%------------------------------------------------------------------------------
