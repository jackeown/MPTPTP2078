%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1353+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:32 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 282 expanded)
%              Number of clauses        :   62 (  81 expanded)
%              Number of leaves         :    9 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 (1380 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK2) ),
    inference(resolution,[status(thm)],[c_7,c_13])).

cnf(c_954,plain,
    ( ~ r2_hidden(X0_41,u1_pre_topc(sK2))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0_41,sK2) ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_1126,plain,
    ( ~ r2_hidden(sK0(sK2,X0_41),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK0(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK0(sK2,X0_41),sK2) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1131,plain,
    ( r2_hidden(sK0(sK2,X0_41),u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(sK0(sK2,X0_41),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_1133,plain,
    ( r2_hidden(sK0(sK2,sK3),u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(sK0(sK2,sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_960,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r2_hidden(X2_41,X0_41)
    | r2_hidden(X2_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1101,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r2_hidden(sK0(sK2,X0_41),X0_41)
    | r2_hidden(sK0(sK2,X0_41),X1_41) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_1125,plain,
    ( ~ r1_tarski(X0_41,u1_pre_topc(sK2))
    | ~ r2_hidden(sK0(sK2,X0_41),X0_41)
    | r2_hidden(sK0(sK2,X0_41),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1127,plain,
    ( r1_tarski(X0_41,u1_pre_topc(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0_41),X0_41) != iProver_top
    | r2_hidden(sK0(sK2,X0_41),u1_pre_topc(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_1129,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3),u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(sK0(sK2,sK3),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_959,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | m1_subset_1(X0_41,X0_42)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1039,plain,
    ( ~ r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3)
    | m1_subset_1(sK1(sK3,u1_pre_topc(sK2)),X0_42)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_42)) ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_1068,plain,
    ( ~ r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3)
    | m1_subset_1(sK1(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_1069,plain,
    ( r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3) != iProver_top
    | m1_subset_1(sK1(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_8,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_258,plain,
    ( r2_hidden(X0,u1_pre_topc(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0,sK2) ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_955,plain,
    ( r2_hidden(X0_41,u1_pre_topc(sK2))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0_41,sK2) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_1050,plain,
    ( r2_hidden(sK1(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK1(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK1(sK3,u1_pre_topc(sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_1051,plain,
    ( r2_hidden(sK1(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(sK1(sK3,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(sK1(sK3,u1_pre_topc(sK2)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK2)
    | ~ v1_tops_2(X1,sK2) ),
    inference(resolution,[status(thm)],[c_3,c_13])).

cnf(c_342,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v3_pre_topc(X0,sK2)
    | ~ v1_tops_2(X1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_328,c_9])).

cnf(c_950,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v3_pre_topc(X0_41,sK2)
    | ~ v1_tops_2(X1_41,sK2) ),
    inference(subtyping,[status(esa)],[c_342])).

cnf(c_1040,plain,
    ( ~ r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v3_pre_topc(sK1(sK3,u1_pre_topc(sK2)),sK2)
    | ~ v1_tops_2(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_1041,plain,
    ( r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v3_pre_topc(sK1(sK3,u1_pre_topc(sK2)),sK2) = iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_962,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ r2_hidden(sK1(X0_41,X1_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1036,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ r2_hidden(sK1(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_1037,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(sK1(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_961,plain,
    ( r1_tarski(X0_41,X1_41)
    | r2_hidden(sK1(X0_41,X1_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1033,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_1034,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_314,plain,
    ( r2_hidden(sK0(sK2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_tops_2(X0,sK2) ),
    inference(resolution,[status(thm)],[c_1,c_13])).

cnf(c_951,plain,
    ( r2_hidden(sK0(sK2,X0_41),X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_tops_2(X0_41,sK2) ),
    inference(subtyping,[status(esa)],[c_314])).

cnf(c_988,plain,
    ( r2_hidden(sK0(sK2,X0_41),X0_41) = iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v1_tops_2(X0_41,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_990,plain,
    ( r2_hidden(sK0(sK2,sK3),sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v1_tops_2(sK3,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_106,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_107,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_106])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tops_2(X0,sK2) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

cnf(c_475,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[status(thm)],[c_107,c_286])).

cnf(c_476,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v3_pre_topc(sK0(sK2,X0),sK2)
    | v1_tops_2(X0,sK2) ),
    inference(resolution,[status(thm)],[c_0,c_13])).

cnf(c_462,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v3_pre_topc(sK0(sK2,sK3),sK2) ),
    inference(resolution,[status(thm)],[c_107,c_300])).

cnf(c_463,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v3_pre_topc(sK0(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_449,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | r2_hidden(sK0(sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[status(thm)],[c_107,c_314])).

cnf(c_450,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3),sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_213,plain,
    ( r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3)
    | ~ v1_tops_2(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_5,c_107])).

cnf(c_214,plain,
    ( r2_hidden(sK1(sK3,u1_pre_topc(sK2)),sK3) = iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
    | v1_tops_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1133,c_1129,c_1069,c_1051,c_1041,c_1037,c_1034,c_990,c_476,c_463,c_450,c_214,c_16,c_15])).


%------------------------------------------------------------------------------
