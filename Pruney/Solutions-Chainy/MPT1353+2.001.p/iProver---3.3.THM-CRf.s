%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:53 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 478 expanded)
%              Number of clauses        :   78 ( 132 expanded)
%              Number of leaves         :   11 ( 107 expanded)
%              Depth                    :   21
%              Number of atoms          :  480 (2323 expanded)
%              Number of equality atoms :  121 ( 162 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> r1_tarski(X1,u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ r1_tarski(sK4,u1_pre_topc(X0))
          | ~ v1_tops_2(sK4,X0) )
        & ( r1_tarski(sK4,u1_pre_topc(X0))
          | v1_tops_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(sK3))
            | ~ v1_tops_2(X1,sK3) )
          & ( r1_tarski(X1,u1_pre_topc(sK3))
            | v1_tops_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r1_tarski(sK4,u1_pre_topc(sK3))
      | ~ v1_tops_2(sK4,sK3) )
    & ( r1_tarski(sK4,u1_pre_topc(sK3))
      | v1_tops_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f10])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,
    ( r1_tarski(sK4,u1_pre_topc(sK3))
    | v1_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,
    ( ~ r1_tarski(sK4,u1_pre_topc(sK3))
    | ~ v1_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2313,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2316,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2672,plain,
    ( r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_2316])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2323,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2322,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3567,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_2322])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2318,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4540,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(X2)) != iProver_top
    | r1_tarski(sK0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_2318])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2317,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( ~ v1_tops_2(X0,X1)
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_274,plain,
    ( ~ v1_tops_2(X0,X1)
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X2,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_275,plain,
    ( ~ v1_tops_2(X0,sK3)
    | v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_2312,plain,
    ( v1_tops_2(X0,sK3) != iProver_top
    | v3_pre_topc(X1,sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_2807,plain,
    ( v1_tops_2(sK4,sK3) != iProver_top
    | v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_2312])).

cnf(c_16,negated_conjecture,
    ( v1_tops_2(sK4,sK3)
    | r1_tarski(sK4,u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1108,plain,
    ( v1_tops_2(sK4,sK3)
    | r1_tarski(sK4,u1_pre_topc(sK3)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_1345,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(X0,X1)
    | r1_tarski(sK4,u1_pre_topc(sK3))
    | sK3 != sK3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1108,c_275])).

cnf(c_1346,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(X0,sK4)
    | r1_tarski(sK4,u1_pre_topc(sK3)) ),
    inference(unflattening,[status(thm)],[c_1345])).

cnf(c_15,negated_conjecture,
    ( ~ v1_tops_2(sK4,sK3)
    | ~ r1_tarski(sK4,u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_355,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_356,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,u1_pre_topc(sK3)) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_160,plain,
    ( v1_tops_2(sK4,sK3)
    | r1_tarski(sK4,u1_pre_topc(sK3)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_535,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(X0,X1)
    | r1_tarski(sK4,u1_pre_topc(sK3))
    | sK3 != sK3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_160,c_275])).

cnf(c_536,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(X0,sK4)
    | r1_tarski(sK4,u1_pre_topc(sK3)) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_916,plain,
    ( v1_tops_2(sK4,sK3)
    | ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | u1_pre_topc(sK3) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_160])).

cnf(c_917,plain,
    ( v1_tops_2(sK4,sK3)
    | r2_hidden(X0,u1_pre_topc(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_1348,plain,
    ( ~ r2_hidden(X0,sK4)
    | v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1346,c_17,c_15,c_356,c_536,c_917])).

cnf(c_1349,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,sK4) ),
    inference(renaming,[status(thm)],[c_1348])).

cnf(c_1350,plain,
    ( v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1349])).

cnf(c_2886,plain,
    ( v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2807,c_1350])).

cnf(c_2893,plain,
    ( v3_pre_topc(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2317,c_2886])).

cnf(c_5449,plain,
    ( v3_pre_topc(sK0(X0,X1),sK3) = iProver_top
    | r2_hidden(sK0(X0,X1),sK4) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_2893])).

cnf(c_6281,plain,
    ( v3_pre_topc(sK0(sK4,X0),sK3) = iProver_top
    | r2_hidden(sK0(sK4,X0),sK4) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2672,c_5449])).

cnf(c_2599,plain,
    ( r2_hidden(sK0(sK4,X0),sK4)
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2615,plain,
    ( r2_hidden(sK0(sK4,X0),sK4) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2599])).

cnf(c_6358,plain,
    ( v3_pre_topc(sK0(sK4,X0),sK3) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6281,c_2615])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_340,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_341,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,u1_pre_topc(sK3)) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_2308,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_2680,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK3)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2317,c_2308])).

cnf(c_5448,plain,
    ( v3_pre_topc(sK0(X0,X1),sK3) != iProver_top
    | r2_hidden(sK0(X0,X1),u1_pre_topc(sK3)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_2680])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2324,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6541,plain,
    ( v3_pre_topc(sK0(X0,u1_pre_topc(sK3)),sK3) != iProver_top
    | r1_tarski(X0,u1_pre_topc(sK3)) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5448,c_2324])).

cnf(c_7108,plain,
    ( r1_tarski(sK4,u1_pre_topc(sK3)) = iProver_top
    | r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6358,c_6541])).

cnf(c_13,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_295,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_296,plain,
    ( v1_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_2311,plain,
    ( v1_tops_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_3131,plain,
    ( v1_tops_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(sK2(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_2316])).

cnf(c_3983,plain,
    ( v1_tops_2(sK4,sK3) = iProver_top
    | r1_tarski(sK2(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_3131])).

cnf(c_21,plain,
    ( v1_tops_2(sK4,sK3) = iProver_top
    | r1_tarski(sK4,u1_pre_topc(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( v1_tops_2(X0,X1)
    | ~ v3_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_325,plain,
    ( v1_tops_2(X0,X1)
    | ~ v3_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_326,plain,
    ( v1_tops_2(X0,sK3)
    | ~ v3_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_2309,plain,
    ( v1_tops_2(X0,sK3) = iProver_top
    | v3_pre_topc(sK2(sK3,X0),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_2507,plain,
    ( v1_tops_2(sK4,sK3) = iProver_top
    | v3_pre_topc(sK2(sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_2309])).

cnf(c_12,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_310,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_311,plain,
    ( v1_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | r2_hidden(sK2(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_2310,plain,
    ( v1_tops_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(sK2(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_2645,plain,
    ( v1_tops_2(sK4,sK3) = iProver_top
    | r2_hidden(sK2(sK3,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_2310])).

cnf(c_3570,plain,
    ( v1_tops_2(sK4,sK3) = iProver_top
    | r2_hidden(sK2(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2645,c_2322])).

cnf(c_2307,plain,
    ( v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_2681,plain,
    ( v3_pre_topc(X0,sK3) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2317,c_2307])).

cnf(c_3857,plain,
    ( v1_tops_2(sK4,sK3) = iProver_top
    | v3_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | r1_tarski(sK2(sK3,sK4),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK4,u1_pre_topc(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_2681])).

cnf(c_4156,plain,
    ( v1_tops_2(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3983,c_21,c_2507,c_3857])).

cnf(c_22,plain,
    ( v1_tops_2(sK4,sK3) != iProver_top
    | r1_tarski(sK4,u1_pre_topc(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7108,c_4156,c_2672,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:50:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.15/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/0.99  
% 2.15/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/0.99  
% 2.15/0.99  ------  iProver source info
% 2.15/0.99  
% 2.15/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.15/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/0.99  git: non_committed_changes: false
% 2.15/0.99  git: last_make_outside_of_git: false
% 2.15/0.99  
% 2.15/0.99  ------ 
% 2.15/0.99  
% 2.15/0.99  ------ Input Options
% 2.15/0.99  
% 2.15/0.99  --out_options                           all
% 2.15/0.99  --tptp_safe_out                         true
% 2.15/0.99  --problem_path                          ""
% 2.15/0.99  --include_path                          ""
% 2.15/0.99  --clausifier                            res/vclausify_rel
% 2.15/0.99  --clausifier_options                    --mode clausify
% 2.15/0.99  --stdin                                 false
% 2.15/0.99  --stats_out                             all
% 2.15/0.99  
% 2.15/0.99  ------ General Options
% 2.15/0.99  
% 2.15/0.99  --fof                                   false
% 2.15/0.99  --time_out_real                         305.
% 2.15/0.99  --time_out_virtual                      -1.
% 2.15/0.99  --symbol_type_check                     false
% 2.15/0.99  --clausify_out                          false
% 2.15/0.99  --sig_cnt_out                           false
% 2.15/0.99  --trig_cnt_out                          false
% 2.15/0.99  --trig_cnt_out_tolerance                1.
% 2.15/0.99  --trig_cnt_out_sk_spl                   false
% 2.15/0.99  --abstr_cl_out                          false
% 2.15/0.99  
% 2.15/0.99  ------ Global Options
% 2.15/0.99  
% 2.15/0.99  --schedule                              default
% 2.15/0.99  --add_important_lit                     false
% 2.15/0.99  --prop_solver_per_cl                    1000
% 2.15/0.99  --min_unsat_core                        false
% 2.15/0.99  --soft_assumptions                      false
% 2.15/0.99  --soft_lemma_size                       3
% 2.15/0.99  --prop_impl_unit_size                   0
% 2.15/0.99  --prop_impl_unit                        []
% 2.15/0.99  --share_sel_clauses                     true
% 2.15/0.99  --reset_solvers                         false
% 2.15/0.99  --bc_imp_inh                            [conj_cone]
% 2.15/0.99  --conj_cone_tolerance                   3.
% 2.15/0.99  --extra_neg_conj                        none
% 2.15/0.99  --large_theory_mode                     true
% 2.15/0.99  --prolific_symb_bound                   200
% 2.15/0.99  --lt_threshold                          2000
% 2.15/0.99  --clause_weak_htbl                      true
% 2.15/0.99  --gc_record_bc_elim                     false
% 2.15/0.99  
% 2.15/0.99  ------ Preprocessing Options
% 2.15/0.99  
% 2.15/0.99  --preprocessing_flag                    true
% 2.15/0.99  --time_out_prep_mult                    0.1
% 2.15/0.99  --splitting_mode                        input
% 2.15/0.99  --splitting_grd                         true
% 2.15/0.99  --splitting_cvd                         false
% 2.15/0.99  --splitting_cvd_svl                     false
% 2.15/0.99  --splitting_nvd                         32
% 2.15/0.99  --sub_typing                            true
% 2.15/0.99  --prep_gs_sim                           true
% 2.15/0.99  --prep_unflatten                        true
% 2.15/0.99  --prep_res_sim                          true
% 2.15/0.99  --prep_upred                            true
% 2.15/0.99  --prep_sem_filter                       exhaustive
% 2.15/0.99  --prep_sem_filter_out                   false
% 2.15/0.99  --pred_elim                             true
% 2.15/0.99  --res_sim_input                         true
% 2.15/0.99  --eq_ax_congr_red                       true
% 2.15/0.99  --pure_diseq_elim                       true
% 2.15/0.99  --brand_transform                       false
% 2.15/0.99  --non_eq_to_eq                          false
% 2.15/0.99  --prep_def_merge                        true
% 2.15/0.99  --prep_def_merge_prop_impl              false
% 2.15/0.99  --prep_def_merge_mbd                    true
% 2.15/0.99  --prep_def_merge_tr_red                 false
% 2.15/0.99  --prep_def_merge_tr_cl                  false
% 2.15/0.99  --smt_preprocessing                     true
% 2.15/0.99  --smt_ac_axioms                         fast
% 2.15/0.99  --preprocessed_out                      false
% 2.15/0.99  --preprocessed_stats                    false
% 2.15/0.99  
% 2.15/0.99  ------ Abstraction refinement Options
% 2.15/0.99  
% 2.15/0.99  --abstr_ref                             []
% 2.15/0.99  --abstr_ref_prep                        false
% 2.15/0.99  --abstr_ref_until_sat                   false
% 2.15/0.99  --abstr_ref_sig_restrict                funpre
% 2.15/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/0.99  --abstr_ref_under                       []
% 2.15/0.99  
% 2.15/0.99  ------ SAT Options
% 2.15/0.99  
% 2.15/0.99  --sat_mode                              false
% 2.15/0.99  --sat_fm_restart_options                ""
% 2.15/0.99  --sat_gr_def                            false
% 2.15/0.99  --sat_epr_types                         true
% 2.15/0.99  --sat_non_cyclic_types                  false
% 2.15/0.99  --sat_finite_models                     false
% 2.15/0.99  --sat_fm_lemmas                         false
% 2.15/0.99  --sat_fm_prep                           false
% 2.15/0.99  --sat_fm_uc_incr                        true
% 2.15/0.99  --sat_out_model                         small
% 2.15/0.99  --sat_out_clauses                       false
% 2.15/0.99  
% 2.15/0.99  ------ QBF Options
% 2.15/0.99  
% 2.15/0.99  --qbf_mode                              false
% 2.15/0.99  --qbf_elim_univ                         false
% 2.15/0.99  --qbf_dom_inst                          none
% 2.15/0.99  --qbf_dom_pre_inst                      false
% 2.15/0.99  --qbf_sk_in                             false
% 2.15/0.99  --qbf_pred_elim                         true
% 2.15/0.99  --qbf_split                             512
% 2.15/0.99  
% 2.15/0.99  ------ BMC1 Options
% 2.15/0.99  
% 2.15/0.99  --bmc1_incremental                      false
% 2.15/0.99  --bmc1_axioms                           reachable_all
% 2.15/0.99  --bmc1_min_bound                        0
% 2.15/0.99  --bmc1_max_bound                        -1
% 2.15/0.99  --bmc1_max_bound_default                -1
% 2.15/0.99  --bmc1_symbol_reachability              true
% 2.15/0.99  --bmc1_property_lemmas                  false
% 2.15/0.99  --bmc1_k_induction                      false
% 2.15/0.99  --bmc1_non_equiv_states                 false
% 2.15/0.99  --bmc1_deadlock                         false
% 2.15/0.99  --bmc1_ucm                              false
% 2.15/0.99  --bmc1_add_unsat_core                   none
% 2.15/1.00  --bmc1_unsat_core_children              false
% 2.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.00  --bmc1_out_stat                         full
% 2.15/1.00  --bmc1_ground_init                      false
% 2.15/1.00  --bmc1_pre_inst_next_state              false
% 2.15/1.00  --bmc1_pre_inst_state                   false
% 2.15/1.00  --bmc1_pre_inst_reach_state             false
% 2.15/1.00  --bmc1_out_unsat_core                   false
% 2.15/1.00  --bmc1_aig_witness_out                  false
% 2.15/1.00  --bmc1_verbose                          false
% 2.15/1.00  --bmc1_dump_clauses_tptp                false
% 2.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.00  --bmc1_dump_file                        -
% 2.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.00  --bmc1_ucm_extend_mode                  1
% 2.15/1.00  --bmc1_ucm_init_mode                    2
% 2.15/1.00  --bmc1_ucm_cone_mode                    none
% 2.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.00  --bmc1_ucm_relax_model                  4
% 2.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.00  --bmc1_ucm_layered_model                none
% 2.15/1.00  --bmc1_ucm_max_lemma_size               10
% 2.15/1.00  
% 2.15/1.00  ------ AIG Options
% 2.15/1.00  
% 2.15/1.00  --aig_mode                              false
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation Options
% 2.15/1.00  
% 2.15/1.00  --instantiation_flag                    true
% 2.15/1.00  --inst_sos_flag                         false
% 2.15/1.00  --inst_sos_phase                        true
% 2.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel_side                     num_symb
% 2.15/1.00  --inst_solver_per_active                1400
% 2.15/1.00  --inst_solver_calls_frac                1.
% 2.15/1.00  --inst_passive_queue_type               priority_queues
% 2.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.00  --inst_passive_queues_freq              [25;2]
% 2.15/1.00  --inst_dismatching                      true
% 2.15/1.00  --inst_eager_unprocessed_to_passive     true
% 2.15/1.00  --inst_prop_sim_given                   true
% 2.15/1.00  --inst_prop_sim_new                     false
% 2.15/1.00  --inst_subs_new                         false
% 2.15/1.00  --inst_eq_res_simp                      false
% 2.15/1.00  --inst_subs_given                       false
% 2.15/1.00  --inst_orphan_elimination               true
% 2.15/1.00  --inst_learning_loop_flag               true
% 2.15/1.00  --inst_learning_start                   3000
% 2.15/1.00  --inst_learning_factor                  2
% 2.15/1.00  --inst_start_prop_sim_after_learn       3
% 2.15/1.00  --inst_sel_renew                        solver
% 2.15/1.00  --inst_lit_activity_flag                true
% 2.15/1.00  --inst_restr_to_given                   false
% 2.15/1.00  --inst_activity_threshold               500
% 2.15/1.00  --inst_out_proof                        true
% 2.15/1.00  
% 2.15/1.00  ------ Resolution Options
% 2.15/1.00  
% 2.15/1.00  --resolution_flag                       true
% 2.15/1.00  --res_lit_sel                           adaptive
% 2.15/1.00  --res_lit_sel_side                      none
% 2.15/1.00  --res_ordering                          kbo
% 2.15/1.00  --res_to_prop_solver                    active
% 2.15/1.00  --res_prop_simpl_new                    false
% 2.15/1.00  --res_prop_simpl_given                  true
% 2.15/1.00  --res_passive_queue_type                priority_queues
% 2.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.00  --res_passive_queues_freq               [15;5]
% 2.15/1.00  --res_forward_subs                      full
% 2.15/1.00  --res_backward_subs                     full
% 2.15/1.00  --res_forward_subs_resolution           true
% 2.15/1.00  --res_backward_subs_resolution          true
% 2.15/1.00  --res_orphan_elimination                true
% 2.15/1.00  --res_time_limit                        2.
% 2.15/1.00  --res_out_proof                         true
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Options
% 2.15/1.00  
% 2.15/1.00  --superposition_flag                    true
% 2.15/1.00  --sup_passive_queue_type                priority_queues
% 2.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.00  --demod_completeness_check              fast
% 2.15/1.00  --demod_use_ground                      true
% 2.15/1.00  --sup_to_prop_solver                    passive
% 2.15/1.00  --sup_prop_simpl_new                    true
% 2.15/1.00  --sup_prop_simpl_given                  true
% 2.15/1.00  --sup_fun_splitting                     false
% 2.15/1.00  --sup_smt_interval                      50000
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Simplification Setup
% 2.15/1.00  
% 2.15/1.00  --sup_indices_passive                   []
% 2.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_full_bw                           [BwDemod]
% 2.15/1.00  --sup_immed_triv                        [TrivRules]
% 2.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_immed_bw_main                     []
% 2.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  
% 2.15/1.00  ------ Combination Options
% 2.15/1.00  
% 2.15/1.00  --comb_res_mult                         3
% 2.15/1.00  --comb_sup_mult                         2
% 2.15/1.00  --comb_inst_mult                        10
% 2.15/1.00  
% 2.15/1.00  ------ Debug Options
% 2.15/1.00  
% 2.15/1.00  --dbg_backtrace                         false
% 2.15/1.00  --dbg_dump_prop_clauses                 false
% 2.15/1.00  --dbg_dump_prop_clauses_file            -
% 2.15/1.00  --dbg_out_stat                          false
% 2.15/1.00  ------ Parsing...
% 2.15/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/1.00  ------ Proving...
% 2.15/1.00  ------ Problem Properties 
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  clauses                                 18
% 2.15/1.00  conjectures                             3
% 2.15/1.00  EPR                                     1
% 2.15/1.00  Horn                                    13
% 2.15/1.00  unary                                   1
% 2.15/1.00  binary                                  8
% 2.15/1.00  lits                                    46
% 2.15/1.00  lits eq                                 2
% 2.15/1.00  fd_pure                                 0
% 2.15/1.00  fd_pseudo                               0
% 2.15/1.00  fd_cond                                 0
% 2.15/1.00  fd_pseudo_cond                          2
% 2.15/1.00  AC symbols                              0
% 2.15/1.00  
% 2.15/1.00  ------ Schedule dynamic 5 is on 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  ------ 
% 2.15/1.00  Current options:
% 2.15/1.00  ------ 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options
% 2.15/1.00  
% 2.15/1.00  --out_options                           all
% 2.15/1.00  --tptp_safe_out                         true
% 2.15/1.00  --problem_path                          ""
% 2.15/1.00  --include_path                          ""
% 2.15/1.00  --clausifier                            res/vclausify_rel
% 2.15/1.00  --clausifier_options                    --mode clausify
% 2.15/1.00  --stdin                                 false
% 2.15/1.00  --stats_out                             all
% 2.15/1.00  
% 2.15/1.00  ------ General Options
% 2.15/1.00  
% 2.15/1.00  --fof                                   false
% 2.15/1.00  --time_out_real                         305.
% 2.15/1.00  --time_out_virtual                      -1.
% 2.15/1.00  --symbol_type_check                     false
% 2.15/1.00  --clausify_out                          false
% 2.15/1.00  --sig_cnt_out                           false
% 2.15/1.00  --trig_cnt_out                          false
% 2.15/1.00  --trig_cnt_out_tolerance                1.
% 2.15/1.00  --trig_cnt_out_sk_spl                   false
% 2.15/1.00  --abstr_cl_out                          false
% 2.15/1.00  
% 2.15/1.00  ------ Global Options
% 2.15/1.00  
% 2.15/1.00  --schedule                              default
% 2.15/1.00  --add_important_lit                     false
% 2.15/1.00  --prop_solver_per_cl                    1000
% 2.15/1.00  --min_unsat_core                        false
% 2.15/1.00  --soft_assumptions                      false
% 2.15/1.00  --soft_lemma_size                       3
% 2.15/1.00  --prop_impl_unit_size                   0
% 2.15/1.00  --prop_impl_unit                        []
% 2.15/1.00  --share_sel_clauses                     true
% 2.15/1.00  --reset_solvers                         false
% 2.15/1.00  --bc_imp_inh                            [conj_cone]
% 2.15/1.00  --conj_cone_tolerance                   3.
% 2.15/1.00  --extra_neg_conj                        none
% 2.15/1.00  --large_theory_mode                     true
% 2.15/1.00  --prolific_symb_bound                   200
% 2.15/1.00  --lt_threshold                          2000
% 2.15/1.00  --clause_weak_htbl                      true
% 2.15/1.00  --gc_record_bc_elim                     false
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing Options
% 2.15/1.00  
% 2.15/1.00  --preprocessing_flag                    true
% 2.15/1.00  --time_out_prep_mult                    0.1
% 2.15/1.00  --splitting_mode                        input
% 2.15/1.00  --splitting_grd                         true
% 2.15/1.00  --splitting_cvd                         false
% 2.15/1.00  --splitting_cvd_svl                     false
% 2.15/1.00  --splitting_nvd                         32
% 2.15/1.00  --sub_typing                            true
% 2.15/1.00  --prep_gs_sim                           true
% 2.15/1.00  --prep_unflatten                        true
% 2.15/1.00  --prep_res_sim                          true
% 2.15/1.00  --prep_upred                            true
% 2.15/1.00  --prep_sem_filter                       exhaustive
% 2.15/1.00  --prep_sem_filter_out                   false
% 2.15/1.00  --pred_elim                             true
% 2.15/1.00  --res_sim_input                         true
% 2.15/1.00  --eq_ax_congr_red                       true
% 2.15/1.00  --pure_diseq_elim                       true
% 2.15/1.00  --brand_transform                       false
% 2.15/1.00  --non_eq_to_eq                          false
% 2.15/1.00  --prep_def_merge                        true
% 2.15/1.00  --prep_def_merge_prop_impl              false
% 2.15/1.00  --prep_def_merge_mbd                    true
% 2.15/1.00  --prep_def_merge_tr_red                 false
% 2.15/1.00  --prep_def_merge_tr_cl                  false
% 2.15/1.00  --smt_preprocessing                     true
% 2.15/1.00  --smt_ac_axioms                         fast
% 2.15/1.00  --preprocessed_out                      false
% 2.15/1.00  --preprocessed_stats                    false
% 2.15/1.00  
% 2.15/1.00  ------ Abstraction refinement Options
% 2.15/1.00  
% 2.15/1.00  --abstr_ref                             []
% 2.15/1.00  --abstr_ref_prep                        false
% 2.15/1.00  --abstr_ref_until_sat                   false
% 2.15/1.00  --abstr_ref_sig_restrict                funpre
% 2.15/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.00  --abstr_ref_under                       []
% 2.15/1.00  
% 2.15/1.00  ------ SAT Options
% 2.15/1.00  
% 2.15/1.00  --sat_mode                              false
% 2.15/1.00  --sat_fm_restart_options                ""
% 2.15/1.00  --sat_gr_def                            false
% 2.15/1.00  --sat_epr_types                         true
% 2.15/1.00  --sat_non_cyclic_types                  false
% 2.15/1.00  --sat_finite_models                     false
% 2.15/1.00  --sat_fm_lemmas                         false
% 2.15/1.00  --sat_fm_prep                           false
% 2.15/1.00  --sat_fm_uc_incr                        true
% 2.15/1.00  --sat_out_model                         small
% 2.15/1.00  --sat_out_clauses                       false
% 2.15/1.00  
% 2.15/1.00  ------ QBF Options
% 2.15/1.00  
% 2.15/1.00  --qbf_mode                              false
% 2.15/1.00  --qbf_elim_univ                         false
% 2.15/1.00  --qbf_dom_inst                          none
% 2.15/1.00  --qbf_dom_pre_inst                      false
% 2.15/1.00  --qbf_sk_in                             false
% 2.15/1.00  --qbf_pred_elim                         true
% 2.15/1.00  --qbf_split                             512
% 2.15/1.00  
% 2.15/1.00  ------ BMC1 Options
% 2.15/1.00  
% 2.15/1.00  --bmc1_incremental                      false
% 2.15/1.00  --bmc1_axioms                           reachable_all
% 2.15/1.00  --bmc1_min_bound                        0
% 2.15/1.00  --bmc1_max_bound                        -1
% 2.15/1.00  --bmc1_max_bound_default                -1
% 2.15/1.00  --bmc1_symbol_reachability              true
% 2.15/1.00  --bmc1_property_lemmas                  false
% 2.15/1.00  --bmc1_k_induction                      false
% 2.15/1.00  --bmc1_non_equiv_states                 false
% 2.15/1.00  --bmc1_deadlock                         false
% 2.15/1.00  --bmc1_ucm                              false
% 2.15/1.00  --bmc1_add_unsat_core                   none
% 2.15/1.00  --bmc1_unsat_core_children              false
% 2.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.00  --bmc1_out_stat                         full
% 2.15/1.00  --bmc1_ground_init                      false
% 2.15/1.00  --bmc1_pre_inst_next_state              false
% 2.15/1.00  --bmc1_pre_inst_state                   false
% 2.15/1.00  --bmc1_pre_inst_reach_state             false
% 2.15/1.00  --bmc1_out_unsat_core                   false
% 2.15/1.00  --bmc1_aig_witness_out                  false
% 2.15/1.00  --bmc1_verbose                          false
% 2.15/1.00  --bmc1_dump_clauses_tptp                false
% 2.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.00  --bmc1_dump_file                        -
% 2.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.00  --bmc1_ucm_extend_mode                  1
% 2.15/1.00  --bmc1_ucm_init_mode                    2
% 2.15/1.00  --bmc1_ucm_cone_mode                    none
% 2.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.00  --bmc1_ucm_relax_model                  4
% 2.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.00  --bmc1_ucm_layered_model                none
% 2.15/1.00  --bmc1_ucm_max_lemma_size               10
% 2.15/1.00  
% 2.15/1.00  ------ AIG Options
% 2.15/1.00  
% 2.15/1.00  --aig_mode                              false
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation Options
% 2.15/1.00  
% 2.15/1.00  --instantiation_flag                    true
% 2.15/1.00  --inst_sos_flag                         false
% 2.15/1.00  --inst_sos_phase                        true
% 2.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel_side                     none
% 2.15/1.00  --inst_solver_per_active                1400
% 2.15/1.00  --inst_solver_calls_frac                1.
% 2.15/1.00  --inst_passive_queue_type               priority_queues
% 2.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.00  --inst_passive_queues_freq              [25;2]
% 2.15/1.00  --inst_dismatching                      true
% 2.15/1.00  --inst_eager_unprocessed_to_passive     true
% 2.15/1.00  --inst_prop_sim_given                   true
% 2.15/1.00  --inst_prop_sim_new                     false
% 2.15/1.00  --inst_subs_new                         false
% 2.15/1.00  --inst_eq_res_simp                      false
% 2.15/1.00  --inst_subs_given                       false
% 2.15/1.00  --inst_orphan_elimination               true
% 2.15/1.00  --inst_learning_loop_flag               true
% 2.15/1.00  --inst_learning_start                   3000
% 2.15/1.00  --inst_learning_factor                  2
% 2.15/1.00  --inst_start_prop_sim_after_learn       3
% 2.15/1.00  --inst_sel_renew                        solver
% 2.15/1.00  --inst_lit_activity_flag                true
% 2.15/1.00  --inst_restr_to_given                   false
% 2.15/1.00  --inst_activity_threshold               500
% 2.15/1.00  --inst_out_proof                        true
% 2.15/1.00  
% 2.15/1.00  ------ Resolution Options
% 2.15/1.00  
% 2.15/1.00  --resolution_flag                       false
% 2.15/1.00  --res_lit_sel                           adaptive
% 2.15/1.00  --res_lit_sel_side                      none
% 2.15/1.00  --res_ordering                          kbo
% 2.15/1.00  --res_to_prop_solver                    active
% 2.15/1.00  --res_prop_simpl_new                    false
% 2.15/1.00  --res_prop_simpl_given                  true
% 2.15/1.00  --res_passive_queue_type                priority_queues
% 2.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.00  --res_passive_queues_freq               [15;5]
% 2.15/1.00  --res_forward_subs                      full
% 2.15/1.00  --res_backward_subs                     full
% 2.15/1.00  --res_forward_subs_resolution           true
% 2.15/1.00  --res_backward_subs_resolution          true
% 2.15/1.00  --res_orphan_elimination                true
% 2.15/1.00  --res_time_limit                        2.
% 2.15/1.00  --res_out_proof                         true
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Options
% 2.15/1.00  
% 2.15/1.00  --superposition_flag                    true
% 2.15/1.00  --sup_passive_queue_type                priority_queues
% 2.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.00  --demod_completeness_check              fast
% 2.15/1.00  --demod_use_ground                      true
% 2.15/1.00  --sup_to_prop_solver                    passive
% 2.15/1.00  --sup_prop_simpl_new                    true
% 2.15/1.00  --sup_prop_simpl_given                  true
% 2.15/1.00  --sup_fun_splitting                     false
% 2.15/1.00  --sup_smt_interval                      50000
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Simplification Setup
% 2.15/1.00  
% 2.15/1.00  --sup_indices_passive                   []
% 2.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_full_bw                           [BwDemod]
% 2.15/1.00  --sup_immed_triv                        [TrivRules]
% 2.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_immed_bw_main                     []
% 2.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  
% 2.15/1.00  ------ Combination Options
% 2.15/1.00  
% 2.15/1.00  --comb_res_mult                         3
% 2.15/1.00  --comb_sup_mult                         2
% 2.15/1.00  --comb_inst_mult                        10
% 2.15/1.00  
% 2.15/1.00  ------ Debug Options
% 2.15/1.00  
% 2.15/1.00  --dbg_backtrace                         false
% 2.15/1.00  --dbg_dump_prop_clauses                 false
% 2.15/1.00  --dbg_dump_prop_clauses_file            -
% 2.15/1.00  --dbg_out_stat                          false
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  ------ Proving...
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  % SZS status Theorem for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  fof(f6,conjecture,(
% 2.15/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f7,negated_conjecture,(
% 2.15/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 2.15/1.00    inference(negated_conjecture,[],[f6])).
% 2.15/1.00  
% 2.15/1.00  fof(f12,plain,(
% 2.15/1.00    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> r1_tarski(X1,u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f7])).
% 2.15/1.00  
% 2.15/1.00  fof(f27,plain,(
% 2.15/1.00    ? [X0] : (? [X1] : (((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.15/1.00    inference(nnf_transformation,[],[f12])).
% 2.15/1.00  
% 2.15/1.00  fof(f28,plain,(
% 2.15/1.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.15/1.00    inference(flattening,[],[f27])).
% 2.15/1.00  
% 2.15/1.00  fof(f30,plain,(
% 2.15/1.00    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => ((~r1_tarski(sK4,u1_pre_topc(X0)) | ~v1_tops_2(sK4,X0)) & (r1_tarski(sK4,u1_pre_topc(X0)) | v1_tops_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f29,plain,(
% 2.15/1.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,u1_pre_topc(sK3)) | ~v1_tops_2(X1,sK3)) & (r1_tarski(X1,u1_pre_topc(sK3)) | v1_tops_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f31,plain,(
% 2.15/1.00    ((~r1_tarski(sK4,u1_pre_topc(sK3)) | ~v1_tops_2(sK4,sK3)) & (r1_tarski(sK4,u1_pre_topc(sK3)) | v1_tops_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3)),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).
% 2.15/1.00  
% 2.15/1.00  fof(f48,plain,(
% 2.15/1.00    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 2.15/1.00    inference(cnf_transformation,[],[f31])).
% 2.15/1.00  
% 2.15/1.00  fof(f3,axiom,(
% 2.15/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f21,plain,(
% 2.15/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.15/1.00    inference(nnf_transformation,[],[f3])).
% 2.15/1.00  
% 2.15/1.00  fof(f39,plain,(
% 2.15/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.15/1.00    inference(cnf_transformation,[],[f21])).
% 2.15/1.00  
% 2.15/1.00  fof(f1,axiom,(
% 2.15/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f8,plain,(
% 2.15/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f1])).
% 2.15/1.00  
% 2.15/1.00  fof(f13,plain,(
% 2.15/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/1.00    inference(nnf_transformation,[],[f8])).
% 2.15/1.00  
% 2.15/1.00  fof(f14,plain,(
% 2.15/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/1.00    inference(rectify,[],[f13])).
% 2.15/1.00  
% 2.15/1.00  fof(f15,plain,(
% 2.15/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f16,plain,(
% 2.15/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 2.15/1.00  
% 2.15/1.00  fof(f33,plain,(
% 2.15/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f16])).
% 2.15/1.00  
% 2.15/1.00  fof(f32,plain,(
% 2.15/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f16])).
% 2.15/1.00  
% 2.15/1.00  fof(f2,axiom,(
% 2.15/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f17,plain,(
% 2.15/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.15/1.00    inference(nnf_transformation,[],[f2])).
% 2.15/1.00  
% 2.15/1.00  fof(f18,plain,(
% 2.15/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.15/1.00    inference(rectify,[],[f17])).
% 2.15/1.00  
% 2.15/1.00  fof(f19,plain,(
% 2.15/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f20,plain,(
% 2.15/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 2.15/1.00  
% 2.15/1.00  fof(f35,plain,(
% 2.15/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.15/1.00    inference(cnf_transformation,[],[f20])).
% 2.15/1.00  
% 2.15/1.00  fof(f52,plain,(
% 2.15/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.15/1.00    inference(equality_resolution,[],[f35])).
% 2.15/1.00  
% 2.15/1.00  fof(f40,plain,(
% 2.15/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f21])).
% 2.15/1.00  
% 2.15/1.00  fof(f5,axiom,(
% 2.15/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f10,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f5])).
% 2.15/1.00  
% 2.15/1.00  fof(f11,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.15/1.00    inference(flattening,[],[f10])).
% 2.15/1.00  
% 2.15/1.00  fof(f23,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.15/1.00    inference(nnf_transformation,[],[f11])).
% 2.15/1.00  
% 2.15/1.00  fof(f24,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.15/1.00    inference(rectify,[],[f23])).
% 2.15/1.00  
% 2.15/1.00  fof(f25,plain,(
% 2.15/1.00    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f26,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 2.15/1.00  
% 2.15/1.00  fof(f43,plain,(
% 2.15/1.00    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f26])).
% 2.15/1.00  
% 2.15/1.00  fof(f47,plain,(
% 2.15/1.00    l1_pre_topc(sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f31])).
% 2.15/1.00  
% 2.15/1.00  fof(f49,plain,(
% 2.15/1.00    r1_tarski(sK4,u1_pre_topc(sK3)) | v1_tops_2(sK4,sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f31])).
% 2.15/1.00  
% 2.15/1.00  fof(f50,plain,(
% 2.15/1.00    ~r1_tarski(sK4,u1_pre_topc(sK3)) | ~v1_tops_2(sK4,sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f31])).
% 2.15/1.00  
% 2.15/1.00  fof(f4,axiom,(
% 2.15/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f9,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f4])).
% 2.15/1.00  
% 2.15/1.00  fof(f22,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.15/1.00    inference(nnf_transformation,[],[f9])).
% 2.15/1.00  
% 2.15/1.00  fof(f42,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f22])).
% 2.15/1.00  
% 2.15/1.00  fof(f41,plain,(
% 2.15/1.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f22])).
% 2.15/1.00  
% 2.15/1.00  fof(f34,plain,(
% 2.15/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f16])).
% 2.15/1.00  
% 2.15/1.00  fof(f44,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f26])).
% 2.15/1.00  
% 2.15/1.00  fof(f46,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f26])).
% 2.15/1.00  
% 2.15/1.00  fof(f45,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f26])).
% 2.15/1.00  
% 2.15/1.00  cnf(c_17,negated_conjecture,
% 2.15/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 2.15/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2313,plain,
% 2.15/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_8,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2316,plain,
% 2.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.15/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2672,plain,
% 2.15/1.00      ( r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2313,c_2316]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1,plain,
% 2.15/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2323,plain,
% 2.15/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.15/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2,plain,
% 2.15/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.15/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2322,plain,
% 2.15/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.15/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.15/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3567,plain,
% 2.15/1.00      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.15/1.00      | r1_tarski(X0,X2) != iProver_top
% 2.15/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2323,c_2322]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_6,plain,
% 2.15/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2318,plain,
% 2.15/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.15/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_4540,plain,
% 2.15/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.15/1.00      | r1_tarski(X0,k1_zfmisc_1(X2)) != iProver_top
% 2.15/1.00      | r1_tarski(sK0(X0,X1),X2) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_3567,c_2318]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_7,plain,
% 2.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2317,plain,
% 2.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.15/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_14,plain,
% 2.15/1.00      ( ~ v1_tops_2(X0,X1)
% 2.15/1.00      | v3_pre_topc(X2,X1)
% 2.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.15/1.00      | ~ r2_hidden(X2,X0)
% 2.15/1.00      | ~ l1_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_18,negated_conjecture,
% 2.15/1.00      ( l1_pre_topc(sK3) ),
% 2.15/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_274,plain,
% 2.15/1.00      ( ~ v1_tops_2(X0,X1)
% 2.15/1.00      | v3_pre_topc(X2,X1)
% 2.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.15/1.00      | ~ r2_hidden(X2,X0)
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_275,plain,
% 2.15/1.00      ( ~ v1_tops_2(X0,sK3)
% 2.15/1.00      | v3_pre_topc(X1,sK3)
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.15/1.00      | ~ r2_hidden(X1,X0) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_274]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2312,plain,
% 2.15/1.00      ( v1_tops_2(X0,sK3) != iProver_top
% 2.15/1.00      | v3_pre_topc(X1,sK3) = iProver_top
% 2.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 2.15/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2807,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) != iProver_top
% 2.15/1.00      | v3_pre_topc(X0,sK3) = iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2313,c_2312]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_16,negated_conjecture,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) | r1_tarski(sK4,u1_pre_topc(sK3)) ),
% 2.15/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1108,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) | r1_tarski(sK4,u1_pre_topc(sK3)) ),
% 2.15/1.00      inference(prop_impl,[status(thm)],[c_16]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1345,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.15/1.00      | ~ r2_hidden(X0,X1)
% 2.15/1.00      | r1_tarski(sK4,u1_pre_topc(sK3))
% 2.15/1.00      | sK3 != sK3
% 2.15/1.00      | sK4 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_1108,c_275]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1346,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.15/1.00      | ~ r2_hidden(X0,sK4)
% 2.15/1.00      | r1_tarski(sK4,u1_pre_topc(sK3)) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_1345]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_15,negated_conjecture,
% 2.15/1.00      ( ~ v1_tops_2(sK4,sK3) | ~ r1_tarski(sK4,u1_pre_topc(sK3)) ),
% 2.15/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_9,plain,
% 2.15/1.00      ( v3_pre_topc(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.15/1.00      | ~ l1_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_355,plain,
% 2.15/1.00      ( v3_pre_topc(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_356,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ r2_hidden(X0,u1_pre_topc(sK3)) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_355]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_160,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) | r1_tarski(sK4,u1_pre_topc(sK3)) ),
% 2.15/1.00      inference(prop_impl,[status(thm)],[c_16]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_535,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.15/1.00      | ~ r2_hidden(X0,X1)
% 2.15/1.00      | r1_tarski(sK4,u1_pre_topc(sK3))
% 2.15/1.00      | sK3 != sK3
% 2.15/1.00      | sK4 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_160,c_275]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_536,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.15/1.00      | ~ r2_hidden(X0,sK4)
% 2.15/1.00      | r1_tarski(sK4,u1_pre_topc(sK3)) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_535]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_916,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3)
% 2.15/1.00      | ~ r2_hidden(X0,X1)
% 2.15/1.00      | r2_hidden(X0,X2)
% 2.15/1.00      | u1_pre_topc(sK3) != X2
% 2.15/1.00      | sK4 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_160]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_917,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3)
% 2.15/1.00      | r2_hidden(X0,u1_pre_topc(sK3))
% 2.15/1.00      | ~ r2_hidden(X0,sK4) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_916]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1348,plain,
% 2.15/1.00      ( ~ r2_hidden(X0,sK4)
% 2.15/1.00      | v3_pre_topc(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_1346,c_17,c_15,c_356,c_536,c_917]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1349,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ r2_hidden(X0,sK4) ),
% 2.15/1.00      inference(renaming,[status(thm)],[c_1348]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1350,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3) = iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1349]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2886,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3) = iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_2807,c_1350]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2893,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3) = iProver_top
% 2.15/1.00      | r2_hidden(X0,sK4) != iProver_top
% 2.15/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2317,c_2886]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_5449,plain,
% 2.15/1.00      ( v3_pre_topc(sK0(X0,X1),sK3) = iProver_top
% 2.15/1.00      | r2_hidden(sK0(X0,X1),sK4) != iProver_top
% 2.15/1.00      | r1_tarski(X0,X1) = iProver_top
% 2.15/1.00      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_4540,c_2893]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_6281,plain,
% 2.15/1.00      ( v3_pre_topc(sK0(sK4,X0),sK3) = iProver_top
% 2.15/1.00      | r2_hidden(sK0(sK4,X0),sK4) != iProver_top
% 2.15/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2672,c_5449]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2599,plain,
% 2.15/1.00      ( r2_hidden(sK0(sK4,X0),sK4) | r1_tarski(sK4,X0) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2615,plain,
% 2.15/1.00      ( r2_hidden(sK0(sK4,X0),sK4) = iProver_top
% 2.15/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_2599]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_6358,plain,
% 2.15/1.00      ( v3_pre_topc(sK0(sK4,X0),sK3) = iProver_top
% 2.15/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_6281,c_2615]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_10,plain,
% 2.15/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.15/1.00      | ~ l1_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_340,plain,
% 2.15/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_341,plain,
% 2.15/1.00      ( ~ v3_pre_topc(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | r2_hidden(X0,u1_pre_topc(sK3)) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_340]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2308,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | r2_hidden(X0,u1_pre_topc(sK3)) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2680,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 2.15/1.00      | r2_hidden(X0,u1_pre_topc(sK3)) = iProver_top
% 2.15/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2317,c_2308]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_5448,plain,
% 2.15/1.00      ( v3_pre_topc(sK0(X0,X1),sK3) != iProver_top
% 2.15/1.00      | r2_hidden(sK0(X0,X1),u1_pre_topc(sK3)) = iProver_top
% 2.15/1.00      | r1_tarski(X0,X1) = iProver_top
% 2.15/1.00      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_4540,c_2680]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_0,plain,
% 2.15/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2324,plain,
% 2.15/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.15/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_6541,plain,
% 2.15/1.00      ( v3_pre_topc(sK0(X0,u1_pre_topc(sK3)),sK3) != iProver_top
% 2.15/1.00      | r1_tarski(X0,u1_pre_topc(sK3)) = iProver_top
% 2.15/1.00      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_5448,c_2324]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_7108,plain,
% 2.15/1.00      ( r1_tarski(sK4,u1_pre_topc(sK3)) = iProver_top
% 2.15/1.00      | r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_6358,c_6541]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_13,plain,
% 2.15/1.00      ( v1_tops_2(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.15/1.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ l1_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_295,plain,
% 2.15/1.00      ( v1_tops_2(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.15/1.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_296,plain,
% 2.15/1.00      ( v1_tops_2(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.15/1.00      | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_295]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2311,plain,
% 2.15/1.00      ( v1_tops_2(X0,sK3) = iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 2.15/1.00      | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3131,plain,
% 2.15/1.00      ( v1_tops_2(X0,sK3) = iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 2.15/1.00      | r1_tarski(sK2(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2311,c_2316]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3983,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) = iProver_top
% 2.15/1.00      | r1_tarski(sK2(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2313,c_3131]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_21,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) = iProver_top
% 2.15/1.00      | r1_tarski(sK4,u1_pre_topc(sK3)) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_11,plain,
% 2.15/1.00      ( v1_tops_2(X0,X1)
% 2.15/1.00      | ~ v3_pre_topc(sK2(X1,X0),X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.15/1.00      | ~ l1_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_325,plain,
% 2.15/1.00      ( v1_tops_2(X0,X1)
% 2.15/1.00      | ~ v3_pre_topc(sK2(X1,X0),X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_326,plain,
% 2.15/1.00      ( v1_tops_2(X0,sK3)
% 2.15/1.00      | ~ v3_pre_topc(sK2(sK3,X0),sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_325]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2309,plain,
% 2.15/1.00      ( v1_tops_2(X0,sK3) = iProver_top
% 2.15/1.00      | v3_pre_topc(sK2(sK3,X0),sK3) != iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2507,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) = iProver_top
% 2.15/1.00      | v3_pre_topc(sK2(sK3,sK4),sK3) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2313,c_2309]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_12,plain,
% 2.15/1.00      ( v1_tops_2(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.15/1.00      | r2_hidden(sK2(X1,X0),X0)
% 2.15/1.00      | ~ l1_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_310,plain,
% 2.15/1.00      ( v1_tops_2(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.15/1.00      | r2_hidden(sK2(X1,X0),X0)
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_311,plain,
% 2.15/1.00      ( v1_tops_2(X0,sK3)
% 2.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.15/1.00      | r2_hidden(sK2(sK3,X0),X0) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_310]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2310,plain,
% 2.15/1.00      ( v1_tops_2(X0,sK3) = iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 2.15/1.00      | r2_hidden(sK2(sK3,X0),X0) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2645,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) = iProver_top
% 2.15/1.00      | r2_hidden(sK2(sK3,sK4),sK4) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2313,c_2310]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3570,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) = iProver_top
% 2.15/1.00      | r2_hidden(sK2(sK3,sK4),X0) = iProver_top
% 2.15/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2645,c_2322]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2307,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3) = iProver_top
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2681,plain,
% 2.15/1.00      ( v3_pre_topc(X0,sK3) = iProver_top
% 2.15/1.00      | r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
% 2.15/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_2317,c_2307]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3857,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) = iProver_top
% 2.15/1.00      | v3_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 2.15/1.00      | r1_tarski(sK2(sK3,sK4),u1_struct_0(sK3)) != iProver_top
% 2.15/1.00      | r1_tarski(sK4,u1_pre_topc(sK3)) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_3570,c_2681]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_4156,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) = iProver_top ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_3983,c_21,c_2507,c_3857]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_22,plain,
% 2.15/1.00      ( v1_tops_2(sK4,sK3) != iProver_top
% 2.15/1.00      | r1_tarski(sK4,u1_pre_topc(sK3)) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(contradiction,plain,
% 2.15/1.00      ( $false ),
% 2.15/1.00      inference(minisat,[status(thm)],[c_7108,c_4156,c_2672,c_22]) ).
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  ------                               Statistics
% 2.15/1.00  
% 2.15/1.00  ------ General
% 2.15/1.00  
% 2.15/1.00  abstr_ref_over_cycles:                  0
% 2.15/1.00  abstr_ref_under_cycles:                 0
% 2.15/1.00  gc_basic_clause_elim:                   0
% 2.15/1.00  forced_gc_time:                         0
% 2.15/1.00  parsing_time:                           0.008
% 2.15/1.00  unif_index_cands_time:                  0.
% 2.15/1.00  unif_index_add_time:                    0.
% 2.15/1.00  orderings_time:                         0.
% 2.15/1.00  out_proof_time:                         0.014
% 2.15/1.00  total_time:                             0.206
% 2.15/1.00  num_of_symbols:                         45
% 2.15/1.00  num_of_terms:                           4152
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing
% 2.15/1.00  
% 2.15/1.00  num_of_splits:                          0
% 2.15/1.00  num_of_split_atoms:                     0
% 2.15/1.00  num_of_reused_defs:                     0
% 2.15/1.00  num_eq_ax_congr_red:                    17
% 2.15/1.00  num_of_sem_filtered_clauses:            1
% 2.15/1.00  num_of_subtypes:                        0
% 2.15/1.00  monotx_restored_types:                  0
% 2.15/1.00  sat_num_of_epr_types:                   0
% 2.15/1.00  sat_num_of_non_cyclic_types:            0
% 2.15/1.00  sat_guarded_non_collapsed_types:        0
% 2.15/1.00  num_pure_diseq_elim:                    0
% 2.15/1.00  simp_replaced_by:                       0
% 2.15/1.00  res_preprocessed:                       96
% 2.15/1.00  prep_upred:                             0
% 2.15/1.00  prep_unflattend:                        96
% 2.15/1.00  smt_new_axioms:                         0
% 2.15/1.00  pred_elim_cands:                        5
% 2.15/1.00  pred_elim:                              1
% 2.15/1.00  pred_elim_cl:                           1
% 2.15/1.00  pred_elim_cycles:                       7
% 2.15/1.00  merged_defs:                            24
% 2.15/1.00  merged_defs_ncl:                        0
% 2.15/1.00  bin_hyper_res:                          24
% 2.15/1.00  prep_cycles:                            4
% 2.15/1.00  pred_elim_time:                         0.018
% 2.15/1.00  splitting_time:                         0.
% 2.15/1.00  sem_filter_time:                        0.
% 2.15/1.00  monotx_time:                            0.
% 2.15/1.00  subtype_inf_time:                       0.
% 2.15/1.00  
% 2.15/1.00  ------ Problem properties
% 2.15/1.00  
% 2.15/1.00  clauses:                                18
% 2.15/1.00  conjectures:                            3
% 2.15/1.00  epr:                                    1
% 2.15/1.00  horn:                                   13
% 2.15/1.00  ground:                                 3
% 2.15/1.00  unary:                                  1
% 2.15/1.00  binary:                                 8
% 2.15/1.00  lits:                                   46
% 2.15/1.00  lits_eq:                                2
% 2.15/1.00  fd_pure:                                0
% 2.15/1.00  fd_pseudo:                              0
% 2.15/1.00  fd_cond:                                0
% 2.15/1.00  fd_pseudo_cond:                         2
% 2.15/1.00  ac_symbols:                             0
% 2.15/1.00  
% 2.15/1.00  ------ Propositional Solver
% 2.15/1.00  
% 2.15/1.00  prop_solver_calls:                      29
% 2.15/1.00  prop_fast_solver_calls:                 1016
% 2.15/1.00  smt_solver_calls:                       0
% 2.15/1.00  smt_fast_solver_calls:                  0
% 2.15/1.00  prop_num_of_clauses:                    2200
% 2.15/1.00  prop_preprocess_simplified:             5657
% 2.15/1.00  prop_fo_subsumed:                       19
% 2.15/1.00  prop_solver_time:                       0.
% 2.15/1.00  smt_solver_time:                        0.
% 2.15/1.00  smt_fast_solver_time:                   0.
% 2.15/1.00  prop_fast_solver_time:                  0.
% 2.15/1.00  prop_unsat_core_time:                   0.
% 2.15/1.00  
% 2.15/1.00  ------ QBF
% 2.15/1.00  
% 2.15/1.00  qbf_q_res:                              0
% 2.15/1.00  qbf_num_tautologies:                    0
% 2.15/1.00  qbf_prep_cycles:                        0
% 2.15/1.00  
% 2.15/1.00  ------ BMC1
% 2.15/1.00  
% 2.15/1.00  bmc1_current_bound:                     -1
% 2.15/1.00  bmc1_last_solved_bound:                 -1
% 2.15/1.00  bmc1_unsat_core_size:                   -1
% 2.15/1.00  bmc1_unsat_core_parents_size:           -1
% 2.15/1.00  bmc1_merge_next_fun:                    0
% 2.15/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation
% 2.15/1.00  
% 2.15/1.00  inst_num_of_clauses:                    534
% 2.15/1.00  inst_num_in_passive:                    251
% 2.15/1.00  inst_num_in_active:                     257
% 2.15/1.00  inst_num_in_unprocessed:                26
% 2.15/1.00  inst_num_of_loops:                      350
% 2.15/1.00  inst_num_of_learning_restarts:          0
% 2.15/1.00  inst_num_moves_active_passive:          88
% 2.15/1.00  inst_lit_activity:                      0
% 2.15/1.00  inst_lit_activity_moves:                0
% 2.15/1.00  inst_num_tautologies:                   0
% 2.15/1.00  inst_num_prop_implied:                  0
% 2.15/1.00  inst_num_existing_simplified:           0
% 2.15/1.00  inst_num_eq_res_simplified:             0
% 2.15/1.00  inst_num_child_elim:                    0
% 2.15/1.00  inst_num_of_dismatching_blockings:      262
% 2.15/1.00  inst_num_of_non_proper_insts:           649
% 2.15/1.00  inst_num_of_duplicates:                 0
% 2.15/1.00  inst_inst_num_from_inst_to_res:         0
% 2.15/1.00  inst_dismatching_checking_time:         0.
% 2.15/1.00  
% 2.15/1.00  ------ Resolution
% 2.15/1.00  
% 2.15/1.00  res_num_of_clauses:                     0
% 2.15/1.00  res_num_in_passive:                     0
% 2.15/1.00  res_num_in_active:                      0
% 2.15/1.00  res_num_of_loops:                       100
% 2.15/1.00  res_forward_subset_subsumed:            3
% 2.15/1.00  res_backward_subset_subsumed:           0
% 2.15/1.00  res_forward_subsumed:                   0
% 2.15/1.00  res_backward_subsumed:                  0
% 2.15/1.00  res_forward_subsumption_resolution:     1
% 2.15/1.00  res_backward_subsumption_resolution:    0
% 2.15/1.00  res_clause_to_clause_subsumption:       489
% 2.15/1.00  res_orphan_elimination:                 0
% 2.15/1.00  res_tautology_del:                      95
% 2.15/1.00  res_num_eq_res_simplified:              0
% 2.15/1.00  res_num_sel_changes:                    0
% 2.15/1.00  res_moves_from_active_to_pass:          0
% 2.15/1.00  
% 2.15/1.00  ------ Superposition
% 2.15/1.00  
% 2.15/1.00  sup_time_total:                         0.
% 2.15/1.00  sup_time_generating:                    0.
% 2.15/1.00  sup_time_sim_full:                      0.
% 2.15/1.00  sup_time_sim_immed:                     0.
% 2.15/1.00  
% 2.15/1.00  sup_num_of_clauses:                     115
% 2.15/1.00  sup_num_in_active:                      65
% 2.15/1.00  sup_num_in_passive:                     50
% 2.15/1.00  sup_num_of_loops:                       68
% 2.15/1.00  sup_fw_superposition:                   56
% 2.15/1.00  sup_bw_superposition:                   90
% 2.15/1.00  sup_immediate_simplified:               18
% 2.15/1.00  sup_given_eliminated:                   0
% 2.15/1.00  comparisons_done:                       0
% 2.15/1.00  comparisons_avoided:                    0
% 2.15/1.00  
% 2.15/1.00  ------ Simplifications
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  sim_fw_subset_subsumed:                 6
% 2.15/1.00  sim_bw_subset_subsumed:                 7
% 2.15/1.00  sim_fw_subsumed:                        12
% 2.15/1.00  sim_bw_subsumed:                        0
% 2.15/1.00  sim_fw_subsumption_res:                 0
% 2.15/1.00  sim_bw_subsumption_res:                 0
% 2.15/1.00  sim_tautology_del:                      18
% 2.15/1.00  sim_eq_tautology_del:                   1
% 2.15/1.00  sim_eq_res_simp:                        1
% 2.15/1.00  sim_fw_demodulated:                     0
% 2.15/1.00  sim_bw_demodulated:                     0
% 2.15/1.00  sim_light_normalised:                   0
% 2.15/1.00  sim_joinable_taut:                      0
% 2.15/1.00  sim_joinable_simp:                      0
% 2.15/1.00  sim_ac_normalised:                      0
% 2.15/1.00  sim_smt_subsumption:                    0
% 2.15/1.00  
%------------------------------------------------------------------------------
