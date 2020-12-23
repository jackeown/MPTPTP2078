%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:53 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 278 expanded)
%              Number of clauses        :   61 (  77 expanded)
%              Number of leaves         :    9 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  374 (1372 expanded)
%              Number of equality atoms :   46 (  46 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> r1_tarski(X1,u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ r1_tarski(sK3,u1_pre_topc(X0))
          | ~ v1_tops_2(sK3,X0) )
        & ( r1_tarski(sK3,u1_pre_topc(X0))
          | v1_tops_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(sK2))
            | ~ v1_tops_2(X1,sK2) )
          & ( r1_tarski(X1,u1_pre_topc(sK2))
            | v1_tops_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
      | ~ v1_tops_2(sK3,sK2) )
    & ( r1_tarski(sK3,u1_pre_topc(sK2))
      | v1_tops_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).

fof(f38,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_332,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_pre_topc(sK2)) ),
    inference(resolution,[status(thm)],[c_4,c_13])).

cnf(c_947,plain,
    ( v3_pre_topc(X0_41,sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_41,u1_pre_topc(sK2)) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_1109,plain,
    ( v3_pre_topc(sK1(sK2,X0_41),sK2)
    | ~ m1_subset_1(sK1(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_1114,plain,
    ( v3_pre_topc(sK1(sK2,X0_41),sK2) = iProver_top
    | m1_subset_1(sK1(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_1116,plain,
    ( v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_957,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | r2_hidden(X0_41,X2_41)
    | ~ r1_tarski(X1_41,X2_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1093,plain,
    ( ~ r2_hidden(sK1(sK2,X0_41),X0_41)
    | r2_hidden(sK1(sK2,X0_41),X1_41)
    | ~ r1_tarski(X0_41,X1_41) ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_1108,plain,
    ( ~ r2_hidden(sK1(sK2,X0_41),X0_41)
    | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2))
    | ~ r1_tarski(X0_41,u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1110,plain,
    ( r2_hidden(sK1(sK2,X0_41),X0_41) != iProver_top
    | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) = iProver_top
    | r1_tarski(X0_41,u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1112,plain,
    ( r2_hidden(sK1(sK2,sK3),u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_956,plain,
    ( m1_subset_1(X0_41,X0_43)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
    | ~ r2_hidden(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1040,plain,
    ( m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),X0_43)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_43))
    | ~ r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_1065,plain,
    ( m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_1066,plain,
    ( m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_318,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,u1_pre_topc(sK2)) ),
    inference(resolution,[status(thm)],[c_5,c_13])).

cnf(c_948,plain,
    ( ~ v3_pre_topc(X0_41,sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_41,u1_pre_topc(sK2)) ),
    inference(subtyping,[status(esa)],[c_318])).

cnf(c_1047,plain,
    ( ~ v3_pre_topc(sK0(sK3,u1_pre_topc(sK2)),sK2)
    | ~ m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_1048,plain,
    ( v3_pre_topc(sK0(sK3,u1_pre_topc(sK2)),sK2) != iProver_top
    | m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_9,plain,
    ( ~ v1_tops_2(X0,X1)
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_254,plain,
    ( ~ v1_tops_2(X0,sK2)
    | v3_pre_topc(X1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_9,c_13])).

cnf(c_268,plain,
    ( ~ v1_tops_2(X0,sK2)
    | v3_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_254,c_3])).

cnf(c_952,plain,
    ( ~ v1_tops_2(X0_41,sK2)
    | v3_pre_topc(X1_41,sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_268])).

cnf(c_1036,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | v3_pre_topc(sK0(sK3,u1_pre_topc(sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_1037,plain,
    ( v1_tops_2(sK3,sK2) != iProver_top
    | v3_pre_topc(sK0(sK3,u1_pre_topc(sK2)),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_959,plain,
    ( ~ r2_hidden(sK0(X0_41,X1_41),X1_41)
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1033,plain,
    ( ~ r2_hidden(sK0(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2))
    | r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_1034,plain,
    ( r2_hidden(sK0(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) != iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_958,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1030,plain,
    ( r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3)
    | r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_1031,plain,
    ( r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) = iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_7,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_290,plain,
    ( v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK1(sK2,X0),X0) ),
    inference(resolution,[status(thm)],[c_7,c_13])).

cnf(c_950,plain,
    ( v1_tops_2(X0_41,sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK1(sK2,X0_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_979,plain,
    ( v1_tops_2(X0_41,sK2) = iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,X0_41),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_981,plain,
    ( v1_tops_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,sK3),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_10,negated_conjecture,
    ( ~ v1_tops_2(sK3,sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_106,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_276,plain,
    ( v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_542,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(resolution,[status(thm)],[c_106,c_276])).

cnf(c_543,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_529,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(resolution,[status(thm)],[c_106,c_290])).

cnf(c_530,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,sK3),sK3) = iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_6,plain,
    ( v1_tops_2(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_304,plain,
    ( v1_tops_2(X0,sK2)
    | ~ v3_pre_topc(sK1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[status(thm)],[c_6,c_13])).

cnf(c_516,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(resolution,[status(thm)],[c_106,c_304])).

cnf(c_517,plain,
    ( v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_209,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) ),
    inference(resolution,[status(thm)],[c_1,c_106])).

cnf(c_210,plain,
    ( v1_tops_2(sK3,sK2) != iProver_top
    | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_11,negated_conjecture,
    ( v1_tops_2(sK3,sK2)
    | r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,plain,
    ( v1_tops_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1116,c_1112,c_1066,c_1048,c_1037,c_1034,c_1031,c_981,c_543,c_530,c_517,c_210,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.80/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.80/1.01  
% 0.80/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.80/1.01  
% 0.80/1.01  ------  iProver source info
% 0.80/1.01  
% 0.80/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.80/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.80/1.01  git: non_committed_changes: false
% 0.80/1.01  git: last_make_outside_of_git: false
% 0.80/1.01  
% 0.80/1.01  ------ 
% 0.80/1.01  
% 0.80/1.01  ------ Input Options
% 0.80/1.01  
% 0.80/1.01  --out_options                           all
% 0.80/1.01  --tptp_safe_out                         true
% 0.80/1.01  --problem_path                          ""
% 0.80/1.01  --include_path                          ""
% 0.80/1.01  --clausifier                            res/vclausify_rel
% 0.80/1.01  --clausifier_options                    --mode clausify
% 0.80/1.01  --stdin                                 false
% 0.80/1.01  --stats_out                             all
% 0.80/1.01  
% 0.80/1.01  ------ General Options
% 0.80/1.01  
% 0.80/1.01  --fof                                   false
% 0.80/1.01  --time_out_real                         305.
% 0.80/1.01  --time_out_virtual                      -1.
% 0.80/1.01  --symbol_type_check                     false
% 0.80/1.01  --clausify_out                          false
% 0.80/1.01  --sig_cnt_out                           false
% 0.80/1.01  --trig_cnt_out                          false
% 0.80/1.01  --trig_cnt_out_tolerance                1.
% 0.80/1.01  --trig_cnt_out_sk_spl                   false
% 0.80/1.01  --abstr_cl_out                          false
% 0.80/1.01  
% 0.80/1.01  ------ Global Options
% 0.80/1.01  
% 0.80/1.01  --schedule                              default
% 0.80/1.01  --add_important_lit                     false
% 0.80/1.01  --prop_solver_per_cl                    1000
% 0.80/1.01  --min_unsat_core                        false
% 0.80/1.01  --soft_assumptions                      false
% 0.80/1.01  --soft_lemma_size                       3
% 0.80/1.01  --prop_impl_unit_size                   0
% 0.80/1.01  --prop_impl_unit                        []
% 0.80/1.01  --share_sel_clauses                     true
% 0.80/1.01  --reset_solvers                         false
% 0.80/1.01  --bc_imp_inh                            [conj_cone]
% 0.80/1.01  --conj_cone_tolerance                   3.
% 0.80/1.01  --extra_neg_conj                        none
% 0.80/1.01  --large_theory_mode                     true
% 0.80/1.01  --prolific_symb_bound                   200
% 0.80/1.01  --lt_threshold                          2000
% 0.80/1.01  --clause_weak_htbl                      true
% 0.80/1.01  --gc_record_bc_elim                     false
% 0.80/1.01  
% 0.80/1.01  ------ Preprocessing Options
% 0.80/1.01  
% 0.80/1.01  --preprocessing_flag                    true
% 0.80/1.01  --time_out_prep_mult                    0.1
% 0.80/1.01  --splitting_mode                        input
% 0.80/1.01  --splitting_grd                         true
% 0.80/1.01  --splitting_cvd                         false
% 0.80/1.01  --splitting_cvd_svl                     false
% 0.80/1.01  --splitting_nvd                         32
% 0.80/1.01  --sub_typing                            true
% 0.80/1.01  --prep_gs_sim                           true
% 0.80/1.01  --prep_unflatten                        true
% 0.80/1.01  --prep_res_sim                          true
% 0.80/1.01  --prep_upred                            true
% 0.80/1.01  --prep_sem_filter                       exhaustive
% 0.80/1.01  --prep_sem_filter_out                   false
% 0.80/1.01  --pred_elim                             true
% 0.80/1.01  --res_sim_input                         true
% 0.80/1.01  --eq_ax_congr_red                       true
% 0.80/1.01  --pure_diseq_elim                       true
% 0.80/1.01  --brand_transform                       false
% 0.80/1.01  --non_eq_to_eq                          false
% 0.80/1.01  --prep_def_merge                        true
% 0.80/1.01  --prep_def_merge_prop_impl              false
% 0.80/1.01  --prep_def_merge_mbd                    true
% 0.80/1.01  --prep_def_merge_tr_red                 false
% 0.80/1.01  --prep_def_merge_tr_cl                  false
% 0.80/1.01  --smt_preprocessing                     true
% 0.80/1.01  --smt_ac_axioms                         fast
% 0.80/1.01  --preprocessed_out                      false
% 0.80/1.01  --preprocessed_stats                    false
% 0.80/1.01  
% 0.80/1.01  ------ Abstraction refinement Options
% 0.80/1.01  
% 0.80/1.01  --abstr_ref                             []
% 0.80/1.01  --abstr_ref_prep                        false
% 0.80/1.01  --abstr_ref_until_sat                   false
% 0.80/1.01  --abstr_ref_sig_restrict                funpre
% 0.80/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.80/1.01  --abstr_ref_under                       []
% 0.80/1.01  
% 0.80/1.01  ------ SAT Options
% 0.80/1.01  
% 0.80/1.01  --sat_mode                              false
% 0.80/1.01  --sat_fm_restart_options                ""
% 0.80/1.01  --sat_gr_def                            false
% 0.80/1.01  --sat_epr_types                         true
% 0.80/1.01  --sat_non_cyclic_types                  false
% 0.80/1.01  --sat_finite_models                     false
% 0.80/1.01  --sat_fm_lemmas                         false
% 0.80/1.01  --sat_fm_prep                           false
% 0.80/1.01  --sat_fm_uc_incr                        true
% 0.80/1.01  --sat_out_model                         small
% 0.80/1.01  --sat_out_clauses                       false
% 0.80/1.01  
% 0.80/1.01  ------ QBF Options
% 0.80/1.01  
% 0.80/1.01  --qbf_mode                              false
% 0.80/1.01  --qbf_elim_univ                         false
% 0.80/1.01  --qbf_dom_inst                          none
% 0.80/1.01  --qbf_dom_pre_inst                      false
% 0.80/1.01  --qbf_sk_in                             false
% 0.80/1.01  --qbf_pred_elim                         true
% 0.80/1.01  --qbf_split                             512
% 0.80/1.01  
% 0.80/1.01  ------ BMC1 Options
% 0.80/1.01  
% 0.80/1.01  --bmc1_incremental                      false
% 0.80/1.01  --bmc1_axioms                           reachable_all
% 0.80/1.01  --bmc1_min_bound                        0
% 0.80/1.01  --bmc1_max_bound                        -1
% 0.80/1.01  --bmc1_max_bound_default                -1
% 0.80/1.01  --bmc1_symbol_reachability              true
% 0.80/1.01  --bmc1_property_lemmas                  false
% 0.80/1.01  --bmc1_k_induction                      false
% 0.80/1.01  --bmc1_non_equiv_states                 false
% 0.80/1.01  --bmc1_deadlock                         false
% 0.80/1.01  --bmc1_ucm                              false
% 0.80/1.01  --bmc1_add_unsat_core                   none
% 0.80/1.01  --bmc1_unsat_core_children              false
% 0.80/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.80/1.01  --bmc1_out_stat                         full
% 0.80/1.01  --bmc1_ground_init                      false
% 0.80/1.01  --bmc1_pre_inst_next_state              false
% 0.80/1.01  --bmc1_pre_inst_state                   false
% 0.80/1.01  --bmc1_pre_inst_reach_state             false
% 0.80/1.01  --bmc1_out_unsat_core                   false
% 0.80/1.01  --bmc1_aig_witness_out                  false
% 0.80/1.01  --bmc1_verbose                          false
% 0.80/1.01  --bmc1_dump_clauses_tptp                false
% 0.80/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.80/1.01  --bmc1_dump_file                        -
% 0.80/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.80/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.80/1.01  --bmc1_ucm_extend_mode                  1
% 0.80/1.01  --bmc1_ucm_init_mode                    2
% 0.80/1.01  --bmc1_ucm_cone_mode                    none
% 0.80/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.80/1.01  --bmc1_ucm_relax_model                  4
% 0.80/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.80/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.80/1.01  --bmc1_ucm_layered_model                none
% 0.80/1.01  --bmc1_ucm_max_lemma_size               10
% 0.80/1.01  
% 0.80/1.01  ------ AIG Options
% 0.80/1.01  
% 0.80/1.01  --aig_mode                              false
% 0.80/1.01  
% 0.80/1.01  ------ Instantiation Options
% 0.80/1.01  
% 0.80/1.01  --instantiation_flag                    true
% 0.80/1.01  --inst_sos_flag                         false
% 0.80/1.01  --inst_sos_phase                        true
% 0.80/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.80/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.80/1.01  --inst_lit_sel_side                     num_symb
% 0.80/1.01  --inst_solver_per_active                1400
% 0.80/1.01  --inst_solver_calls_frac                1.
% 0.80/1.01  --inst_passive_queue_type               priority_queues
% 0.80/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.80/1.01  --inst_passive_queues_freq              [25;2]
% 0.80/1.01  --inst_dismatching                      true
% 0.80/1.01  --inst_eager_unprocessed_to_passive     true
% 0.80/1.01  --inst_prop_sim_given                   true
% 0.80/1.01  --inst_prop_sim_new                     false
% 0.80/1.01  --inst_subs_new                         false
% 0.80/1.01  --inst_eq_res_simp                      false
% 0.80/1.01  --inst_subs_given                       false
% 0.80/1.01  --inst_orphan_elimination               true
% 0.80/1.01  --inst_learning_loop_flag               true
% 0.80/1.01  --inst_learning_start                   3000
% 0.80/1.01  --inst_learning_factor                  2
% 0.80/1.01  --inst_start_prop_sim_after_learn       3
% 0.80/1.01  --inst_sel_renew                        solver
% 0.80/1.01  --inst_lit_activity_flag                true
% 0.80/1.01  --inst_restr_to_given                   false
% 0.80/1.01  --inst_activity_threshold               500
% 0.80/1.01  --inst_out_proof                        true
% 0.80/1.01  
% 0.80/1.01  ------ Resolution Options
% 0.80/1.01  
% 0.80/1.01  --resolution_flag                       true
% 0.80/1.01  --res_lit_sel                           adaptive
% 0.80/1.01  --res_lit_sel_side                      none
% 0.80/1.01  --res_ordering                          kbo
% 0.80/1.01  --res_to_prop_solver                    active
% 0.80/1.01  --res_prop_simpl_new                    false
% 0.80/1.01  --res_prop_simpl_given                  true
% 0.80/1.01  --res_passive_queue_type                priority_queues
% 0.80/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.80/1.01  --res_passive_queues_freq               [15;5]
% 0.80/1.01  --res_forward_subs                      full
% 0.80/1.01  --res_backward_subs                     full
% 0.80/1.01  --res_forward_subs_resolution           true
% 0.80/1.01  --res_backward_subs_resolution          true
% 0.80/1.01  --res_orphan_elimination                true
% 0.80/1.01  --res_time_limit                        2.
% 0.80/1.01  --res_out_proof                         true
% 0.80/1.01  
% 0.80/1.01  ------ Superposition Options
% 0.80/1.01  
% 0.80/1.01  --superposition_flag                    true
% 0.80/1.01  --sup_passive_queue_type                priority_queues
% 0.80/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.80/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.80/1.01  --demod_completeness_check              fast
% 0.80/1.01  --demod_use_ground                      true
% 0.80/1.01  --sup_to_prop_solver                    passive
% 0.80/1.01  --sup_prop_simpl_new                    true
% 0.80/1.01  --sup_prop_simpl_given                  true
% 0.80/1.01  --sup_fun_splitting                     false
% 0.80/1.01  --sup_smt_interval                      50000
% 0.80/1.01  
% 0.80/1.01  ------ Superposition Simplification Setup
% 0.80/1.01  
% 0.80/1.01  --sup_indices_passive                   []
% 0.80/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.80/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.01  --sup_full_bw                           [BwDemod]
% 0.80/1.01  --sup_immed_triv                        [TrivRules]
% 0.80/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.80/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.01  --sup_immed_bw_main                     []
% 0.80/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.80/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/1.01  
% 0.80/1.01  ------ Combination Options
% 0.80/1.01  
% 0.80/1.01  --comb_res_mult                         3
% 0.80/1.01  --comb_sup_mult                         2
% 0.80/1.01  --comb_inst_mult                        10
% 0.80/1.01  
% 0.80/1.01  ------ Debug Options
% 0.80/1.01  
% 0.80/1.01  --dbg_backtrace                         false
% 0.80/1.01  --dbg_dump_prop_clauses                 false
% 0.80/1.01  --dbg_dump_prop_clauses_file            -
% 0.80/1.01  --dbg_out_stat                          false
% 0.80/1.01  ------ Parsing...
% 0.80/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.80/1.01  
% 0.80/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.80/1.01  
% 0.80/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.80/1.01  ------ Proving...
% 0.80/1.01  ------ Problem Properties 
% 0.80/1.01  
% 0.80/1.01  
% 0.80/1.01  clauses                                 13
% 0.80/1.01  conjectures                             3
% 0.80/1.01  EPR                                     1
% 0.80/1.01  Horn                                    9
% 0.80/1.01  unary                                   1
% 0.80/1.01  binary                                  4
% 0.80/1.01  lits                                    34
% 0.80/1.01  lits eq                                 0
% 0.80/1.01  fd_pure                                 0
% 0.80/1.01  fd_pseudo                               0
% 0.80/1.01  fd_cond                                 0
% 0.80/1.01  fd_pseudo_cond                          0
% 0.80/1.01  AC symbols                              0
% 0.80/1.01  
% 0.80/1.01  ------ Schedule dynamic 5 is on 
% 0.80/1.01  
% 0.80/1.01  ------ no equalities: superposition off 
% 0.80/1.01  
% 0.80/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.80/1.01  
% 0.80/1.01  
% 0.80/1.01  ------ 
% 0.80/1.01  Current options:
% 0.80/1.01  ------ 
% 0.80/1.01  
% 0.80/1.01  ------ Input Options
% 0.80/1.01  
% 0.80/1.01  --out_options                           all
% 0.80/1.01  --tptp_safe_out                         true
% 0.80/1.01  --problem_path                          ""
% 0.80/1.01  --include_path                          ""
% 0.80/1.01  --clausifier                            res/vclausify_rel
% 0.80/1.01  --clausifier_options                    --mode clausify
% 0.80/1.01  --stdin                                 false
% 0.80/1.01  --stats_out                             all
% 0.80/1.01  
% 0.80/1.01  ------ General Options
% 0.80/1.01  
% 0.80/1.01  --fof                                   false
% 0.80/1.01  --time_out_real                         305.
% 0.80/1.01  --time_out_virtual                      -1.
% 0.80/1.01  --symbol_type_check                     false
% 0.80/1.01  --clausify_out                          false
% 0.80/1.01  --sig_cnt_out                           false
% 0.80/1.01  --trig_cnt_out                          false
% 0.80/1.01  --trig_cnt_out_tolerance                1.
% 0.80/1.01  --trig_cnt_out_sk_spl                   false
% 0.80/1.01  --abstr_cl_out                          false
% 0.80/1.01  
% 0.80/1.01  ------ Global Options
% 0.80/1.01  
% 0.80/1.01  --schedule                              default
% 0.80/1.01  --add_important_lit                     false
% 0.80/1.01  --prop_solver_per_cl                    1000
% 0.80/1.01  --min_unsat_core                        false
% 0.80/1.01  --soft_assumptions                      false
% 0.80/1.01  --soft_lemma_size                       3
% 0.80/1.01  --prop_impl_unit_size                   0
% 0.80/1.01  --prop_impl_unit                        []
% 0.80/1.01  --share_sel_clauses                     true
% 0.80/1.01  --reset_solvers                         false
% 0.80/1.01  --bc_imp_inh                            [conj_cone]
% 0.80/1.01  --conj_cone_tolerance                   3.
% 0.80/1.01  --extra_neg_conj                        none
% 0.80/1.01  --large_theory_mode                     true
% 0.80/1.01  --prolific_symb_bound                   200
% 0.80/1.01  --lt_threshold                          2000
% 0.80/1.01  --clause_weak_htbl                      true
% 0.80/1.01  --gc_record_bc_elim                     false
% 0.80/1.01  
% 0.80/1.01  ------ Preprocessing Options
% 0.80/1.01  
% 0.80/1.01  --preprocessing_flag                    true
% 0.80/1.01  --time_out_prep_mult                    0.1
% 0.80/1.01  --splitting_mode                        input
% 0.80/1.01  --splitting_grd                         true
% 0.80/1.01  --splitting_cvd                         false
% 0.80/1.01  --splitting_cvd_svl                     false
% 0.80/1.01  --splitting_nvd                         32
% 0.80/1.01  --sub_typing                            true
% 0.80/1.01  --prep_gs_sim                           true
% 0.80/1.01  --prep_unflatten                        true
% 0.80/1.01  --prep_res_sim                          true
% 0.80/1.01  --prep_upred                            true
% 0.80/1.01  --prep_sem_filter                       exhaustive
% 0.80/1.01  --prep_sem_filter_out                   false
% 0.80/1.01  --pred_elim                             true
% 0.80/1.01  --res_sim_input                         true
% 0.80/1.01  --eq_ax_congr_red                       true
% 0.80/1.01  --pure_diseq_elim                       true
% 0.80/1.01  --brand_transform                       false
% 0.80/1.01  --non_eq_to_eq                          false
% 0.80/1.01  --prep_def_merge                        true
% 0.80/1.01  --prep_def_merge_prop_impl              false
% 0.80/1.01  --prep_def_merge_mbd                    true
% 0.80/1.01  --prep_def_merge_tr_red                 false
% 0.80/1.01  --prep_def_merge_tr_cl                  false
% 0.80/1.01  --smt_preprocessing                     true
% 0.80/1.01  --smt_ac_axioms                         fast
% 0.80/1.01  --preprocessed_out                      false
% 0.80/1.01  --preprocessed_stats                    false
% 0.80/1.01  
% 0.80/1.01  ------ Abstraction refinement Options
% 0.80/1.01  
% 0.80/1.01  --abstr_ref                             []
% 0.80/1.01  --abstr_ref_prep                        false
% 0.80/1.01  --abstr_ref_until_sat                   false
% 0.80/1.01  --abstr_ref_sig_restrict                funpre
% 0.80/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.80/1.01  --abstr_ref_under                       []
% 0.80/1.01  
% 0.80/1.01  ------ SAT Options
% 0.80/1.01  
% 0.80/1.01  --sat_mode                              false
% 0.80/1.01  --sat_fm_restart_options                ""
% 0.80/1.01  --sat_gr_def                            false
% 0.80/1.01  --sat_epr_types                         true
% 0.80/1.01  --sat_non_cyclic_types                  false
% 0.80/1.01  --sat_finite_models                     false
% 0.80/1.01  --sat_fm_lemmas                         false
% 0.80/1.01  --sat_fm_prep                           false
% 0.80/1.01  --sat_fm_uc_incr                        true
% 0.80/1.01  --sat_out_model                         small
% 0.80/1.01  --sat_out_clauses                       false
% 0.80/1.01  
% 0.80/1.01  ------ QBF Options
% 0.80/1.01  
% 0.80/1.01  --qbf_mode                              false
% 0.80/1.01  --qbf_elim_univ                         false
% 0.80/1.01  --qbf_dom_inst                          none
% 0.80/1.01  --qbf_dom_pre_inst                      false
% 0.80/1.01  --qbf_sk_in                             false
% 0.80/1.01  --qbf_pred_elim                         true
% 0.80/1.01  --qbf_split                             512
% 0.80/1.01  
% 0.80/1.01  ------ BMC1 Options
% 0.80/1.01  
% 0.80/1.01  --bmc1_incremental                      false
% 0.80/1.01  --bmc1_axioms                           reachable_all
% 0.80/1.01  --bmc1_min_bound                        0
% 0.80/1.01  --bmc1_max_bound                        -1
% 0.80/1.01  --bmc1_max_bound_default                -1
% 0.80/1.01  --bmc1_symbol_reachability              true
% 0.80/1.01  --bmc1_property_lemmas                  false
% 0.80/1.01  --bmc1_k_induction                      false
% 0.80/1.01  --bmc1_non_equiv_states                 false
% 0.80/1.01  --bmc1_deadlock                         false
% 0.80/1.01  --bmc1_ucm                              false
% 0.80/1.01  --bmc1_add_unsat_core                   none
% 0.80/1.01  --bmc1_unsat_core_children              false
% 0.80/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.80/1.01  --bmc1_out_stat                         full
% 0.80/1.01  --bmc1_ground_init                      false
% 0.80/1.01  --bmc1_pre_inst_next_state              false
% 0.80/1.01  --bmc1_pre_inst_state                   false
% 0.80/1.01  --bmc1_pre_inst_reach_state             false
% 0.80/1.01  --bmc1_out_unsat_core                   false
% 0.80/1.01  --bmc1_aig_witness_out                  false
% 0.80/1.01  --bmc1_verbose                          false
% 0.80/1.01  --bmc1_dump_clauses_tptp                false
% 0.80/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.80/1.01  --bmc1_dump_file                        -
% 0.80/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.80/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.80/1.01  --bmc1_ucm_extend_mode                  1
% 0.80/1.01  --bmc1_ucm_init_mode                    2
% 0.80/1.01  --bmc1_ucm_cone_mode                    none
% 0.80/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.80/1.01  --bmc1_ucm_relax_model                  4
% 0.80/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.80/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.80/1.01  --bmc1_ucm_layered_model                none
% 0.80/1.01  --bmc1_ucm_max_lemma_size               10
% 0.80/1.01  
% 0.80/1.01  ------ AIG Options
% 0.80/1.01  
% 0.80/1.01  --aig_mode                              false
% 0.80/1.01  
% 0.80/1.01  ------ Instantiation Options
% 0.80/1.01  
% 0.80/1.01  --instantiation_flag                    true
% 0.80/1.01  --inst_sos_flag                         false
% 0.80/1.01  --inst_sos_phase                        true
% 0.80/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.80/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.80/1.01  --inst_lit_sel_side                     none
% 0.80/1.01  --inst_solver_per_active                1400
% 0.80/1.01  --inst_solver_calls_frac                1.
% 0.80/1.01  --inst_passive_queue_type               priority_queues
% 0.80/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.80/1.01  --inst_passive_queues_freq              [25;2]
% 0.80/1.01  --inst_dismatching                      true
% 0.80/1.01  --inst_eager_unprocessed_to_passive     true
% 0.80/1.01  --inst_prop_sim_given                   true
% 0.80/1.01  --inst_prop_sim_new                     false
% 0.80/1.01  --inst_subs_new                         false
% 0.80/1.01  --inst_eq_res_simp                      false
% 0.80/1.01  --inst_subs_given                       false
% 0.80/1.01  --inst_orphan_elimination               true
% 0.80/1.01  --inst_learning_loop_flag               true
% 0.80/1.01  --inst_learning_start                   3000
% 0.80/1.01  --inst_learning_factor                  2
% 0.80/1.01  --inst_start_prop_sim_after_learn       3
% 0.80/1.01  --inst_sel_renew                        solver
% 0.80/1.01  --inst_lit_activity_flag                true
% 0.80/1.01  --inst_restr_to_given                   false
% 0.80/1.01  --inst_activity_threshold               500
% 0.80/1.01  --inst_out_proof                        true
% 0.80/1.01  
% 0.80/1.01  ------ Resolution Options
% 0.80/1.01  
% 0.80/1.01  --resolution_flag                       false
% 0.80/1.01  --res_lit_sel                           adaptive
% 0.80/1.01  --res_lit_sel_side                      none
% 0.80/1.01  --res_ordering                          kbo
% 0.80/1.01  --res_to_prop_solver                    active
% 0.80/1.01  --res_prop_simpl_new                    false
% 0.80/1.01  --res_prop_simpl_given                  true
% 0.80/1.01  --res_passive_queue_type                priority_queues
% 0.80/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.80/1.01  --res_passive_queues_freq               [15;5]
% 0.80/1.01  --res_forward_subs                      full
% 0.80/1.01  --res_backward_subs                     full
% 0.80/1.01  --res_forward_subs_resolution           true
% 0.80/1.01  --res_backward_subs_resolution          true
% 0.80/1.01  --res_orphan_elimination                true
% 0.80/1.01  --res_time_limit                        2.
% 0.80/1.01  --res_out_proof                         true
% 0.80/1.01  
% 0.80/1.01  ------ Superposition Options
% 0.80/1.01  
% 0.80/1.01  --superposition_flag                    false
% 0.80/1.01  --sup_passive_queue_type                priority_queues
% 0.80/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.80/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.80/1.01  --demod_completeness_check              fast
% 0.80/1.01  --demod_use_ground                      true
% 0.80/1.01  --sup_to_prop_solver                    passive
% 0.80/1.01  --sup_prop_simpl_new                    true
% 0.80/1.01  --sup_prop_simpl_given                  true
% 0.80/1.01  --sup_fun_splitting                     false
% 0.80/1.01  --sup_smt_interval                      50000
% 0.80/1.01  
% 0.80/1.01  ------ Superposition Simplification Setup
% 0.80/1.01  
% 0.80/1.01  --sup_indices_passive                   []
% 0.80/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.80/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.01  --sup_full_bw                           [BwDemod]
% 0.80/1.01  --sup_immed_triv                        [TrivRules]
% 0.80/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.80/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.01  --sup_immed_bw_main                     []
% 0.80/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.80/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/1.01  
% 0.80/1.01  ------ Combination Options
% 0.80/1.01  
% 0.80/1.01  --comb_res_mult                         3
% 0.80/1.01  --comb_sup_mult                         2
% 0.80/1.01  --comb_inst_mult                        10
% 0.80/1.01  
% 0.80/1.01  ------ Debug Options
% 0.80/1.01  
% 0.80/1.01  --dbg_backtrace                         false
% 0.80/1.01  --dbg_dump_prop_clauses                 false
% 0.80/1.01  --dbg_dump_prop_clauses_file            -
% 0.80/1.01  --dbg_out_stat                          false
% 0.80/1.01  
% 0.80/1.01  
% 0.80/1.01  
% 0.80/1.01  
% 0.80/1.01  ------ Proving...
% 0.80/1.01  
% 0.80/1.01  
% 0.80/1.01  % SZS status Theorem for theBenchmark.p
% 0.80/1.01  
% 0.80/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.80/1.01  
% 0.80/1.01  fof(f3,axiom,(
% 0.80/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.80/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/1.01  
% 0.80/1.01  fof(f10,plain,(
% 0.80/1.01    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.80/1.01    inference(ennf_transformation,[],[f3])).
% 0.80/1.01  
% 0.80/1.01  fof(f18,plain,(
% 0.80/1.01    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.80/1.01    inference(nnf_transformation,[],[f10])).
% 0.80/1.01  
% 0.80/1.01  fof(f33,plain,(
% 0.80/1.01    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f18])).
% 0.80/1.01  
% 0.80/1.01  fof(f5,conjecture,(
% 0.80/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.80/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/1.01  
% 0.80/1.01  fof(f6,negated_conjecture,(
% 0.80/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.80/1.01    inference(negated_conjecture,[],[f5])).
% 0.80/1.01  
% 0.80/1.01  fof(f13,plain,(
% 0.80/1.01    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> r1_tarski(X1,u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.80/1.01    inference(ennf_transformation,[],[f6])).
% 0.80/1.01  
% 0.80/1.01  fof(f23,plain,(
% 0.80/1.01    ? [X0] : (? [X1] : (((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.80/1.01    inference(nnf_transformation,[],[f13])).
% 0.80/1.01  
% 0.80/1.01  fof(f24,plain,(
% 0.80/1.01    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.80/1.01    inference(flattening,[],[f23])).
% 0.80/1.01  
% 0.80/1.01  fof(f26,plain,(
% 0.80/1.01    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => ((~r1_tarski(sK3,u1_pre_topc(X0)) | ~v1_tops_2(sK3,X0)) & (r1_tarski(sK3,u1_pre_topc(X0)) | v1_tops_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 0.80/1.01    introduced(choice_axiom,[])).
% 0.80/1.01  
% 0.80/1.01  fof(f25,plain,(
% 0.80/1.01    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,u1_pre_topc(sK2)) | ~v1_tops_2(X1,sK2)) & (r1_tarski(X1,u1_pre_topc(sK2)) | v1_tops_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 0.80/1.01    introduced(choice_axiom,[])).
% 0.80/1.01  
% 0.80/1.01  fof(f27,plain,(
% 0.80/1.01    ((~r1_tarski(sK3,u1_pre_topc(sK2)) | ~v1_tops_2(sK3,sK2)) & (r1_tarski(sK3,u1_pre_topc(sK2)) | v1_tops_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 0.80/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).
% 0.80/1.01  
% 0.80/1.01  fof(f38,plain,(
% 0.80/1.01    l1_pre_topc(sK2)),
% 0.80/1.01    inference(cnf_transformation,[],[f27])).
% 0.80/1.01  
% 0.80/1.01  fof(f1,axiom,(
% 0.80/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.80/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/1.01  
% 0.80/1.01  fof(f7,plain,(
% 0.80/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.80/1.01    inference(ennf_transformation,[],[f1])).
% 0.80/1.01  
% 0.80/1.01  fof(f14,plain,(
% 0.80/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.80/1.01    inference(nnf_transformation,[],[f7])).
% 0.80/1.01  
% 0.80/1.01  fof(f15,plain,(
% 0.80/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.80/1.01    inference(rectify,[],[f14])).
% 0.80/1.01  
% 0.80/1.01  fof(f16,plain,(
% 0.80/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.80/1.01    introduced(choice_axiom,[])).
% 0.80/1.01  
% 0.80/1.01  fof(f17,plain,(
% 0.80/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.80/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 0.80/1.01  
% 0.80/1.01  fof(f28,plain,(
% 0.80/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f17])).
% 0.80/1.01  
% 0.80/1.01  fof(f2,axiom,(
% 0.80/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.80/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/1.01  
% 0.80/1.01  fof(f8,plain,(
% 0.80/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.80/1.01    inference(ennf_transformation,[],[f2])).
% 0.80/1.01  
% 0.80/1.01  fof(f9,plain,(
% 0.80/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.80/1.01    inference(flattening,[],[f8])).
% 0.80/1.01  
% 0.80/1.01  fof(f31,plain,(
% 0.80/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f9])).
% 0.80/1.01  
% 0.80/1.01  fof(f32,plain,(
% 0.80/1.01    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f18])).
% 0.80/1.01  
% 0.80/1.01  fof(f4,axiom,(
% 0.80/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.80/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/1.01  
% 0.80/1.01  fof(f11,plain,(
% 0.80/1.01    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.80/1.01    inference(ennf_transformation,[],[f4])).
% 0.80/1.01  
% 0.80/1.01  fof(f12,plain,(
% 0.80/1.01    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.80/1.01    inference(flattening,[],[f11])).
% 0.80/1.01  
% 0.80/1.01  fof(f19,plain,(
% 0.80/1.01    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.80/1.01    inference(nnf_transformation,[],[f12])).
% 0.80/1.01  
% 0.80/1.01  fof(f20,plain,(
% 0.80/1.01    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.80/1.01    inference(rectify,[],[f19])).
% 0.80/1.01  
% 0.80/1.01  fof(f21,plain,(
% 0.80/1.01    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.80/1.01    introduced(choice_axiom,[])).
% 0.80/1.01  
% 0.80/1.01  fof(f22,plain,(
% 0.80/1.01    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.80/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 0.80/1.01  
% 0.80/1.01  fof(f34,plain,(
% 0.80/1.01    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f22])).
% 0.80/1.01  
% 0.80/1.01  fof(f30,plain,(
% 0.80/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f17])).
% 0.80/1.01  
% 0.80/1.01  fof(f29,plain,(
% 0.80/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f17])).
% 0.80/1.01  
% 0.80/1.01  fof(f36,plain,(
% 0.80/1.01    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f22])).
% 0.80/1.01  
% 0.80/1.01  fof(f41,plain,(
% 0.80/1.01    ~r1_tarski(sK3,u1_pre_topc(sK2)) | ~v1_tops_2(sK3,sK2)),
% 0.80/1.01    inference(cnf_transformation,[],[f27])).
% 0.80/1.01  
% 0.80/1.01  fof(f35,plain,(
% 0.80/1.01    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f22])).
% 0.80/1.01  
% 0.80/1.01  fof(f37,plain,(
% 0.80/1.01    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.80/1.01    inference(cnf_transformation,[],[f22])).
% 0.80/1.01  
% 0.80/1.01  fof(f40,plain,(
% 0.80/1.01    r1_tarski(sK3,u1_pre_topc(sK2)) | v1_tops_2(sK3,sK2)),
% 0.80/1.01    inference(cnf_transformation,[],[f27])).
% 0.80/1.01  
% 0.80/1.01  fof(f39,plain,(
% 0.80/1.01    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.80/1.01    inference(cnf_transformation,[],[f27])).
% 0.80/1.01  
% 0.80/1.01  cnf(c_4,plain,
% 0.80/1.01      ( v3_pre_topc(X0,X1)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 0.80/1.01      | ~ l1_pre_topc(X1) ),
% 0.80/1.01      inference(cnf_transformation,[],[f33]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_13,negated_conjecture,
% 0.80/1.01      ( l1_pre_topc(sK2) ),
% 0.80/1.01      inference(cnf_transformation,[],[f38]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_332,plain,
% 0.80/1.01      ( v3_pre_topc(X0,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_4,c_13]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_947,plain,
% 0.80/1.01      ( v3_pre_topc(X0_41,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | ~ r2_hidden(X0_41,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(subtyping,[status(esa)],[c_332]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1109,plain,
% 0.80/1.01      ( v3_pre_topc(sK1(sK2,X0_41),sK2)
% 0.80/1.01      | ~ m1_subset_1(sK1(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | ~ r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_947]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1114,plain,
% 0.80/1.01      ( v3_pre_topc(sK1(sK2,X0_41),sK2) = iProver_top
% 0.80/1.01      | m1_subset_1(sK1(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 0.80/1.01      | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) != iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1116,plain,
% 0.80/1.01      ( v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 0.80/1.01      | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 0.80/1.01      | r2_hidden(sK1(sK2,sK3),u1_pre_topc(sK2)) != iProver_top ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_1114]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_2,plain,
% 0.80/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 0.80/1.01      inference(cnf_transformation,[],[f28]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_957,plain,
% 0.80/1.01      ( ~ r2_hidden(X0_41,X1_41)
% 0.80/1.01      | r2_hidden(X0_41,X2_41)
% 0.80/1.01      | ~ r1_tarski(X1_41,X2_41) ),
% 0.80/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1093,plain,
% 0.80/1.01      ( ~ r2_hidden(sK1(sK2,X0_41),X0_41)
% 0.80/1.01      | r2_hidden(sK1(sK2,X0_41),X1_41)
% 0.80/1.01      | ~ r1_tarski(X0_41,X1_41) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_957]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1108,plain,
% 0.80/1.01      ( ~ r2_hidden(sK1(sK2,X0_41),X0_41)
% 0.80/1.01      | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2))
% 0.80/1.01      | ~ r1_tarski(X0_41,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_1093]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1110,plain,
% 0.80/1.01      ( r2_hidden(sK1(sK2,X0_41),X0_41) != iProver_top
% 0.80/1.01      | r2_hidden(sK1(sK2,X0_41),u1_pre_topc(sK2)) = iProver_top
% 0.80/1.01      | r1_tarski(X0_41,u1_pre_topc(sK2)) != iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1112,plain,
% 0.80/1.01      ( r2_hidden(sK1(sK2,sK3),u1_pre_topc(sK2)) = iProver_top
% 0.80/1.01      | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_1110]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_3,plain,
% 0.80/1.01      ( m1_subset_1(X0,X1)
% 0.80/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 0.80/1.01      | ~ r2_hidden(X0,X2) ),
% 0.80/1.01      inference(cnf_transformation,[],[f31]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_956,plain,
% 0.80/1.01      ( m1_subset_1(X0_41,X0_43)
% 0.80/1.01      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
% 0.80/1.01      | ~ r2_hidden(X0_41,X1_41) ),
% 0.80/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1040,plain,
% 0.80/1.01      ( m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),X0_43)
% 0.80/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_43))
% 0.80/1.01      | ~ r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_956]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1065,plain,
% 0.80/1.01      ( m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | ~ r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_1040]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1066,plain,
% 0.80/1.01      ( m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 0.80/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.80/1.01      | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) != iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_1065]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_5,plain,
% 0.80/1.01      ( ~ v3_pre_topc(X0,X1)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.01      | r2_hidden(X0,u1_pre_topc(X1))
% 0.80/1.01      | ~ l1_pre_topc(X1) ),
% 0.80/1.01      inference(cnf_transformation,[],[f32]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_318,plain,
% 0.80/1.01      ( ~ v3_pre_topc(X0,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | r2_hidden(X0,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_5,c_13]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_948,plain,
% 0.80/1.01      ( ~ v3_pre_topc(X0_41,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | r2_hidden(X0_41,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(subtyping,[status(esa)],[c_318]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1047,plain,
% 0.80/1.01      ( ~ v3_pre_topc(sK0(sK3,u1_pre_topc(sK2)),sK2)
% 0.80/1.01      | ~ m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_948]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1048,plain,
% 0.80/1.01      ( v3_pre_topc(sK0(sK3,u1_pre_topc(sK2)),sK2) != iProver_top
% 0.80/1.01      | m1_subset_1(sK0(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 0.80/1.01      | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) = iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_9,plain,
% 0.80/1.01      ( ~ v1_tops_2(X0,X1)
% 0.80/1.01      | v3_pre_topc(X2,X1)
% 0.80/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.80/1.01      | ~ r2_hidden(X2,X0)
% 0.80/1.01      | ~ l1_pre_topc(X1) ),
% 0.80/1.01      inference(cnf_transformation,[],[f34]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_254,plain,
% 0.80/1.01      ( ~ v1_tops_2(X0,sK2)
% 0.80/1.01      | v3_pre_topc(X1,sK2)
% 0.80/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | ~ r2_hidden(X1,X0) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_9,c_13]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_268,plain,
% 0.80/1.01      ( ~ v1_tops_2(X0,sK2)
% 0.80/1.01      | v3_pre_topc(X1,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | ~ r2_hidden(X1,X0) ),
% 0.80/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_254,c_3]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_952,plain,
% 0.80/1.01      ( ~ v1_tops_2(X0_41,sK2)
% 0.80/1.01      | v3_pre_topc(X1_41,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | ~ r2_hidden(X1_41,X0_41) ),
% 0.80/1.01      inference(subtyping,[status(esa)],[c_268]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1036,plain,
% 0.80/1.01      ( ~ v1_tops_2(sK3,sK2)
% 0.80/1.01      | v3_pre_topc(sK0(sK3,u1_pre_topc(sK2)),sK2)
% 0.80/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | ~ r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_952]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1037,plain,
% 0.80/1.01      ( v1_tops_2(sK3,sK2) != iProver_top
% 0.80/1.01      | v3_pre_topc(sK0(sK3,u1_pre_topc(sK2)),sK2) = iProver_top
% 0.80/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.80/1.01      | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) != iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_0,plain,
% 0.80/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 0.80/1.01      inference(cnf_transformation,[],[f30]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_959,plain,
% 0.80/1.01      ( ~ r2_hidden(sK0(X0_41,X1_41),X1_41) | r1_tarski(X0_41,X1_41) ),
% 0.80/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1033,plain,
% 0.80/1.01      ( ~ r2_hidden(sK0(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2))
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_959]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1034,plain,
% 0.80/1.01      ( r2_hidden(sK0(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) != iProver_top
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1,plain,
% 0.80/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 0.80/1.01      inference(cnf_transformation,[],[f29]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_958,plain,
% 0.80/1.01      ( r2_hidden(sK0(X0_41,X1_41),X0_41) | r1_tarski(X0_41,X1_41) ),
% 0.80/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1030,plain,
% 0.80/1.01      ( r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3)
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_958]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_1031,plain,
% 0.80/1.01      ( r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) = iProver_top
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_1030]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_7,plain,
% 0.80/1.01      ( v1_tops_2(X0,X1)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.80/1.01      | r2_hidden(sK1(X1,X0),X0)
% 0.80/1.01      | ~ l1_pre_topc(X1) ),
% 0.80/1.01      inference(cnf_transformation,[],[f36]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_290,plain,
% 0.80/1.01      ( v1_tops_2(X0,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | r2_hidden(sK1(sK2,X0),X0) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_7,c_13]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_950,plain,
% 0.80/1.01      ( v1_tops_2(X0_41,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | r2_hidden(sK1(sK2,X0_41),X0_41) ),
% 0.80/1.01      inference(subtyping,[status(esa)],[c_290]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_979,plain,
% 0.80/1.01      ( v1_tops_2(X0_41,sK2) = iProver_top
% 0.80/1.01      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.80/1.01      | r2_hidden(sK1(sK2,X0_41),X0_41) = iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_950]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_981,plain,
% 0.80/1.01      ( v1_tops_2(sK3,sK2) = iProver_top
% 0.80/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.80/1.01      | r2_hidden(sK1(sK2,sK3),sK3) = iProver_top ),
% 0.80/1.01      inference(instantiation,[status(thm)],[c_979]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_10,negated_conjecture,
% 0.80/1.01      ( ~ v1_tops_2(sK3,sK2) | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(cnf_transformation,[],[f41]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_106,plain,
% 0.80/1.01      ( ~ v1_tops_2(sK3,sK2) | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(prop_impl,[status(thm)],[c_10]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_8,plain,
% 0.80/1.01      ( v1_tops_2(X0,X1)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.80/1.01      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.80/1.01      | ~ l1_pre_topc(X1) ),
% 0.80/1.01      inference(cnf_transformation,[],[f35]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_276,plain,
% 0.80/1.01      ( v1_tops_2(X0,sK2)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_8,c_13]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_542,plain,
% 0.80/1.01      ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.80/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_106,c_276]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_543,plain,
% 0.80/1.01      ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 0.80/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_529,plain,
% 0.80/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | r2_hidden(sK1(sK2,sK3),sK3)
% 0.80/1.01      | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_106,c_290]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_530,plain,
% 0.80/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.80/1.01      | r2_hidden(sK1(sK2,sK3),sK3) = iProver_top
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_6,plain,
% 0.80/1.01      ( v1_tops_2(X0,X1)
% 0.80/1.01      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.80/1.01      | ~ l1_pre_topc(X1) ),
% 0.80/1.01      inference(cnf_transformation,[],[f37]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_304,plain,
% 0.80/1.01      ( v1_tops_2(X0,sK2)
% 0.80/1.01      | ~ v3_pre_topc(sK1(sK2,X0),sK2)
% 0.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_6,c_13]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_516,plain,
% 0.80/1.01      ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 0.80/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.80/1.01      | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_106,c_304]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_517,plain,
% 0.80/1.01      ( v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top
% 0.80/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_209,plain,
% 0.80/1.01      ( ~ v1_tops_2(sK3,sK2) | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) ),
% 0.80/1.01      inference(resolution,[status(thm)],[c_1,c_106]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_210,plain,
% 0.80/1.01      ( v1_tops_2(sK3,sK2) != iProver_top
% 0.80/1.01      | r2_hidden(sK0(sK3,u1_pre_topc(sK2)),sK3) = iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_11,negated_conjecture,
% 0.80/1.01      ( v1_tops_2(sK3,sK2) | r1_tarski(sK3,u1_pre_topc(sK2)) ),
% 0.80/1.01      inference(cnf_transformation,[],[f40]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_16,plain,
% 0.80/1.01      ( v1_tops_2(sK3,sK2) = iProver_top
% 0.80/1.01      | r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_12,negated_conjecture,
% 0.80/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 0.80/1.01      inference(cnf_transformation,[],[f39]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(c_15,plain,
% 0.80/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 0.80/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.80/1.01  
% 0.80/1.01  cnf(contradiction,plain,
% 0.80/1.01      ( $false ),
% 0.80/1.01      inference(minisat,
% 0.80/1.01                [status(thm)],
% 0.80/1.01                [c_1116,c_1112,c_1066,c_1048,c_1037,c_1034,c_1031,c_981,
% 0.80/1.01                 c_543,c_530,c_517,c_210,c_16,c_15]) ).
% 0.80/1.01  
% 0.80/1.01  
% 0.80/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.80/1.01  
% 0.80/1.01  ------                               Statistics
% 0.80/1.01  
% 0.80/1.01  ------ General
% 0.80/1.01  
% 0.80/1.01  abstr_ref_over_cycles:                  0
% 0.80/1.01  abstr_ref_under_cycles:                 0
% 0.80/1.01  gc_basic_clause_elim:                   0
% 0.80/1.01  forced_gc_time:                         0
% 0.80/1.01  parsing_time:                           0.009
% 0.80/1.01  unif_index_cands_time:                  0.
% 0.80/1.01  unif_index_add_time:                    0.
% 0.80/1.01  orderings_time:                         0.
% 0.80/1.01  out_proof_time:                         0.011
% 0.80/1.01  total_time:                             0.057
% 0.80/1.01  num_of_symbols:                         47
% 0.80/1.01  num_of_terms:                           686
% 0.80/1.01  
% 0.80/1.01  ------ Preprocessing
% 0.80/1.01  
% 0.80/1.01  num_of_splits:                          0
% 0.80/1.01  num_of_split_atoms:                     0
% 0.80/1.01  num_of_reused_defs:                     0
% 0.80/1.01  num_eq_ax_congr_red:                    0
% 0.80/1.01  num_of_sem_filtered_clauses:            0
% 0.80/1.01  num_of_subtypes:                        3
% 0.80/1.01  monotx_restored_types:                  0
% 0.80/1.01  sat_num_of_epr_types:                   0
% 0.80/1.01  sat_num_of_non_cyclic_types:            0
% 0.80/1.01  sat_guarded_non_collapsed_types:        0
% 0.80/1.01  num_pure_diseq_elim:                    0
% 0.80/1.01  simp_replaced_by:                       0
% 0.80/1.01  res_preprocessed:                       27
% 0.80/1.01  prep_upred:                             0
% 0.80/1.01  prep_unflattend:                        0
% 0.80/1.01  smt_new_axioms:                         0
% 0.80/1.01  pred_elim_cands:                        5
% 0.80/1.01  pred_elim:                              1
% 0.80/1.01  pred_elim_cl:                           1
% 0.80/1.01  pred_elim_cycles:                       7
% 0.80/1.01  merged_defs:                            4
% 0.80/1.01  merged_defs_ncl:                        0
% 0.80/1.01  bin_hyper_res:                          4
% 0.80/1.01  prep_cycles:                            2
% 0.80/1.01  pred_elim_time:                         0.009
% 0.80/1.01  splitting_time:                         0.
% 0.80/1.01  sem_filter_time:                        0.
% 0.80/1.01  monotx_time:                            0.
% 0.80/1.01  subtype_inf_time:                       0.
% 0.80/1.01  
% 0.80/1.01  ------ Problem properties
% 0.80/1.01  
% 0.80/1.01  clauses:                                13
% 0.80/1.01  conjectures:                            3
% 0.80/1.01  epr:                                    1
% 0.80/1.01  horn:                                   9
% 0.80/1.01  ground:                                 3
% 0.80/1.01  unary:                                  1
% 0.80/1.01  binary:                                 4
% 0.80/1.01  lits:                                   34
% 0.80/1.01  lits_eq:                                0
% 0.80/1.01  fd_pure:                                0
% 0.80/1.01  fd_pseudo:                              0
% 0.80/1.01  fd_cond:                                0
% 0.80/1.01  fd_pseudo_cond:                         0
% 0.80/1.01  ac_symbols:                             0
% 0.80/1.01  
% 0.80/1.01  ------ Propositional Solver
% 0.80/1.01  
% 0.80/1.01  prop_solver_calls:                      16
% 0.80/1.01  prop_fast_solver_calls:                 304
% 0.80/1.01  smt_solver_calls:                       0
% 0.80/1.01  smt_fast_solver_calls:                  0
% 0.80/1.01  prop_num_of_clauses:                    238
% 0.80/1.01  prop_preprocess_simplified:             1150
% 0.80/1.01  prop_fo_subsumed:                       11
% 0.80/1.01  prop_solver_time:                       0.
% 0.80/1.01  smt_solver_time:                        0.
% 0.80/1.01  smt_fast_solver_time:                   0.
% 0.80/1.01  prop_fast_solver_time:                  0.
% 0.80/1.01  prop_unsat_core_time:                   0.
% 0.80/1.01  
% 0.80/1.01  ------ QBF
% 0.80/1.01  
% 0.80/1.01  qbf_q_res:                              0
% 0.80/1.01  qbf_num_tautologies:                    0
% 0.80/1.01  qbf_prep_cycles:                        0
% 0.80/1.01  
% 0.80/1.01  ------ BMC1
% 0.80/1.01  
% 0.80/1.01  bmc1_current_bound:                     -1
% 0.80/1.01  bmc1_last_solved_bound:                 -1
% 0.80/1.01  bmc1_unsat_core_size:                   -1
% 0.80/1.01  bmc1_unsat_core_parents_size:           -1
% 0.80/1.01  bmc1_merge_next_fun:                    0
% 0.80/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.80/1.01  
% 0.80/1.01  ------ Instantiation
% 0.80/1.01  
% 0.80/1.01  inst_num_of_clauses:                    38
% 0.80/1.01  inst_num_in_passive:                    5
% 0.80/1.01  inst_num_in_active:                     32
% 0.80/1.01  inst_num_in_unprocessed:                0
% 0.80/1.01  inst_num_of_loops:                      48
% 0.80/1.01  inst_num_of_learning_restarts:          0
% 0.80/1.01  inst_num_moves_active_passive:          10
% 0.80/1.01  inst_lit_activity:                      0
% 0.80/1.01  inst_lit_activity_moves:                0
% 0.80/1.01  inst_num_tautologies:                   0
% 0.80/1.01  inst_num_prop_implied:                  0
% 0.80/1.01  inst_num_existing_simplified:           0
% 0.80/1.01  inst_num_eq_res_simplified:             0
% 0.80/1.01  inst_num_child_elim:                    0
% 0.80/1.01  inst_num_of_dismatching_blockings:      2
% 0.80/1.01  inst_num_of_non_proper_insts:           23
% 0.80/1.01  inst_num_of_duplicates:                 0
% 0.80/1.01  inst_inst_num_from_inst_to_res:         0
% 0.80/1.01  inst_dismatching_checking_time:         0.
% 0.80/1.01  
% 0.80/1.01  ------ Resolution
% 0.80/1.01  
% 0.80/1.01  res_num_of_clauses:                     0
% 0.80/1.01  res_num_in_passive:                     0
% 0.80/1.01  res_num_in_active:                      0
% 0.80/1.01  res_num_of_loops:                       29
% 0.80/1.01  res_forward_subset_subsumed:            0
% 0.80/1.01  res_backward_subset_subsumed:           0
% 0.80/1.01  res_forward_subsumed:                   0
% 0.80/1.01  res_backward_subsumed:                  0
% 0.80/1.01  res_forward_subsumption_resolution:     2
% 0.80/1.01  res_backward_subsumption_resolution:    0
% 0.80/1.01  res_clause_to_clause_subsumption:       18
% 0.80/1.01  res_orphan_elimination:                 0
% 0.80/1.01  res_tautology_del:                      15
% 0.80/1.01  res_num_eq_res_simplified:              0
% 0.80/1.01  res_num_sel_changes:                    0
% 0.80/1.01  res_moves_from_active_to_pass:          0
% 0.80/1.01  
% 0.80/1.01  ------ Superposition
% 0.80/1.01  
% 0.80/1.01  sup_time_total:                         0.
% 0.80/1.01  sup_time_generating:                    0.
% 0.80/1.01  sup_time_sim_full:                      0.
% 0.80/1.01  sup_time_sim_immed:                     0.
% 0.80/1.01  
% 0.80/1.01  sup_num_of_clauses:                     0
% 0.80/1.01  sup_num_in_active:                      0
% 0.80/1.01  sup_num_in_passive:                     0
% 0.80/1.01  sup_num_of_loops:                       0
% 0.80/1.01  sup_fw_superposition:                   0
% 0.80/1.01  sup_bw_superposition:                   0
% 0.80/1.01  sup_immediate_simplified:               0
% 0.80/1.01  sup_given_eliminated:                   0
% 0.80/1.01  comparisons_done:                       0
% 0.80/1.01  comparisons_avoided:                    0
% 0.80/1.01  
% 0.80/1.01  ------ Simplifications
% 0.80/1.01  
% 0.80/1.01  
% 0.80/1.01  sim_fw_subset_subsumed:                 0
% 0.80/1.01  sim_bw_subset_subsumed:                 0
% 0.80/1.01  sim_fw_subsumed:                        0
% 0.80/1.01  sim_bw_subsumed:                        0
% 0.80/1.01  sim_fw_subsumption_res:                 0
% 0.80/1.01  sim_bw_subsumption_res:                 0
% 0.80/1.01  sim_tautology_del:                      0
% 0.80/1.01  sim_eq_tautology_del:                   0
% 0.80/1.01  sim_eq_res_simp:                        0
% 0.80/1.01  sim_fw_demodulated:                     0
% 0.80/1.01  sim_bw_demodulated:                     0
% 0.80/1.01  sim_light_normalised:                   0
% 0.80/1.01  sim_joinable_taut:                      0
% 0.80/1.01  sim_joinable_simp:                      0
% 0.80/1.01  sim_ac_normalised:                      0
% 0.80/1.01  sim_smt_subsumption:                    0
% 0.80/1.01  
%------------------------------------------------------------------------------
