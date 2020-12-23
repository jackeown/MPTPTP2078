%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:20 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  174 (1196 expanded)
%              Number of clauses        :  119 ( 250 expanded)
%              Number of leaves         :   15 ( 354 expanded)
%              Depth                    :   23
%              Number of atoms          :  787 (13459 expanded)
%              Number of equality atoms :   99 ( 137 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK4)
        & r1_tarski(sK4,X2)
        & v3_pre_topc(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_connsp_2(X2,X0,X1) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X1,X3)
              | ~ r1_tarski(X3,sK3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_connsp_2(sK3,X0,X1) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,sK3)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | m1_connsp_2(sK3,X0,X1) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(sK2,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,sK2) )
            & ( ? [X4] :
                  ( r2_hidden(sK2,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | m1_connsp_2(X2,X0,sK2) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
                | ~ m1_connsp_2(X2,sK1,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK1)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                | m1_connsp_2(X2,sK1,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK2,X3)
          | ~ r1_tarski(X3,sK3)
          | ~ v3_pre_topc(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ m1_connsp_2(sK3,sK1,sK2) )
    & ( ( r2_hidden(sK2,sK4)
        & r1_tarski(sK4,sK3)
        & v3_pre_topc(sK4,sK1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | m1_connsp_2(sK3,sK1,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f35,f34,f33,f32])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r1_tarski(X3,sK3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_connsp_2(sK3,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,
    ( r1_tarski(sK4,sK3)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,
    ( r2_hidden(sK2,sK4)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( v3_pre_topc(sK4,sK1)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1376,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | r2_hidden(X0_44,X2_44)
    | ~ r1_tarski(X1_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2266,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | r2_hidden(X0_44,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(X1_44,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_2948,plain,
    ( ~ r2_hidden(X0_44,k1_tops_1(sK1,sK4))
    | r2_hidden(X0_44,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_2950,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2948])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1372,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1783,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1372])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_230,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_231,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_235,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_231,c_19,c_18])).

cnf(c_1370,plain,
    ( ~ m1_connsp_2(X0_44,sK1,X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_235])).

cnf(c_1785,plain,
    ( m1_connsp_2(X0_44,sK1,X1_44) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_44,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_2559,plain,
    ( m1_connsp_2(sK3,sK1,X0_44) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_44,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_1785])).

cnf(c_2584,plain,
    ( ~ m1_connsp_2(sK3,sK1,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | r2_hidden(X0_44,k1_tops_1(sK1,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2559])).

cnf(c_2586,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2584])).

cnf(c_1389,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | r2_hidden(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_2007,plain,
    ( r2_hidden(X0_44,X1_44)
    | ~ r2_hidden(sK2,sK4)
    | X1_44 != sK4
    | X0_44 != sK2 ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_2251,plain,
    ( r2_hidden(X0_44,k1_tops_1(sK1,sK4))
    | ~ r2_hidden(sK2,sK4)
    | X0_44 != sK2
    | k1_tops_1(sK1,sK4) != sK4 ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_2253,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ r2_hidden(sK2,sK4)
    | k1_tops_1(sK1,sK4) != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2251])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1368,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1_44,X0_44)
    | r1_tarski(k1_tops_1(sK1,X1_44),k1_tops_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_390])).

cnf(c_1964,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0_44,sK3)
    | r1_tarski(k1_tops_1(sK1,X0_44),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_2197,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
    | ~ r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1964])).

cnf(c_15,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1373,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1782,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_26,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_769,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | sK1 != sK1
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_235])).

cnf(c_770,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_772,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_17,c_16])).

cnf(c_774,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_11,negated_conjecture,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_288,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_289,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_18])).

cnf(c_294,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_537,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r1_tarski(X0,sK3)
    | k1_tops_1(sK1,X1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_294])).

cnf(c_538,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_420])).

cnf(c_543,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
    inference(renaming,[status(thm)],[c_542])).

cnf(c_1362,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0_44))
    | ~ r1_tarski(k1_tops_1(sK1,X0_44),sK3) ),
    inference(subtyping,[status(esa)],[c_543])).

cnf(c_1954,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_1955,plain,
    ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1954])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0_44),X0_44) ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_1961,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_1962,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_2036,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1782,c_25,c_26,c_774,c_1955,c_1962])).

cnf(c_2038,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2036])).

cnf(c_13,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1374,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r1_tarski(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1781,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1374])).

cnf(c_28,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_783,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | r1_tarski(sK4,sK3)
    | sK1 != sK1
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_235])).

cnf(c_784,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_786,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_17,c_16])).

cnf(c_788,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_2002,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1781,c_25,c_28,c_788,c_1955,c_1962])).

cnf(c_2004,plain,
    ( r1_tarski(sK4,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2002])).

cnf(c_12,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1375,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1780,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_29,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | r2_hidden(sK2,sK4)
    | sK1 != sK1
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_235])).

cnf(c_798,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_800,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_17,c_16])).

cnf(c_802,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_1996,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1780,c_25,c_29,c_802,c_1955,c_1962])).

cnf(c_1998,plain,
    ( r2_hidden(sK2,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1996])).

cnf(c_9,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_254,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_255,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_259,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_19,c_18])).

cnf(c_1369,plain,
    ( m1_connsp_2(X0_44,sK1,X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | ~ r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_1969,plain,
    ( m1_connsp_2(sK3,sK1,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_44,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_1971,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_7,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_306,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_307,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_311,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_18])).

cnf(c_312,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_431,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_312])).

cnf(c_432,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_471,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0)
    | ~ r1_tarski(X0,sK3)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(resolution,[status(thm)],[c_432,c_11])).

cnf(c_1365,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0_44)
    | ~ r1_tarski(X0_44,sK3)
    | k1_tops_1(sK1,X0_44) != X0_44 ),
    inference(subtyping,[status(esa)],[c_471])).

cnf(c_1379,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1365])).

cnf(c_1948,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_331,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_332,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_336,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_18])).

cnf(c_337,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_336])).

cnf(c_371,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_337,c_18])).

cnf(c_372,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_14,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_494,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0
    | sK4 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_372,c_14])).

cnf(c_495,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_connsp_2(sK3,sK1,sK2)
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_15])).

cnf(c_500,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_1364,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_1382,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | sP0_iProver_split
    | k1_tops_1(sK1,sK4) = sK4 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1364])).

cnf(c_1386,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1399,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2950,c_2586,c_2253,c_2197,c_2038,c_2004,c_1998,c_1971,c_1961,c_1954,c_1948,c_1382,c_1399,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:34:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.57/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/0.98  
% 1.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.57/0.98  
% 1.57/0.98  ------  iProver source info
% 1.57/0.98  
% 1.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.57/0.98  git: non_committed_changes: false
% 1.57/0.98  git: last_make_outside_of_git: false
% 1.57/0.98  
% 1.57/0.98  ------ 
% 1.57/0.98  
% 1.57/0.98  ------ Input Options
% 1.57/0.98  
% 1.57/0.98  --out_options                           all
% 1.57/0.98  --tptp_safe_out                         true
% 1.57/0.98  --problem_path                          ""
% 1.57/0.98  --include_path                          ""
% 1.57/0.98  --clausifier                            res/vclausify_rel
% 1.57/0.98  --clausifier_options                    --mode clausify
% 1.57/0.98  --stdin                                 false
% 1.57/0.98  --stats_out                             all
% 1.57/0.98  
% 1.57/0.98  ------ General Options
% 1.57/0.98  
% 1.57/0.98  --fof                                   false
% 1.57/0.98  --time_out_real                         305.
% 1.57/0.98  --time_out_virtual                      -1.
% 1.57/0.98  --symbol_type_check                     false
% 1.57/0.98  --clausify_out                          false
% 1.57/0.98  --sig_cnt_out                           false
% 1.57/0.98  --trig_cnt_out                          false
% 1.57/0.98  --trig_cnt_out_tolerance                1.
% 1.57/0.98  --trig_cnt_out_sk_spl                   false
% 1.57/0.98  --abstr_cl_out                          false
% 1.57/0.98  
% 1.57/0.98  ------ Global Options
% 1.57/0.98  
% 1.57/0.98  --schedule                              default
% 1.57/0.98  --add_important_lit                     false
% 1.57/0.98  --prop_solver_per_cl                    1000
% 1.57/0.98  --min_unsat_core                        false
% 1.57/0.98  --soft_assumptions                      false
% 1.57/0.98  --soft_lemma_size                       3
% 1.57/0.98  --prop_impl_unit_size                   0
% 1.57/0.98  --prop_impl_unit                        []
% 1.57/0.98  --share_sel_clauses                     true
% 1.57/0.98  --reset_solvers                         false
% 1.57/0.98  --bc_imp_inh                            [conj_cone]
% 1.57/0.98  --conj_cone_tolerance                   3.
% 1.57/0.98  --extra_neg_conj                        none
% 1.57/0.98  --large_theory_mode                     true
% 1.57/0.98  --prolific_symb_bound                   200
% 1.57/0.98  --lt_threshold                          2000
% 1.57/0.98  --clause_weak_htbl                      true
% 1.57/0.98  --gc_record_bc_elim                     false
% 1.57/0.98  
% 1.57/0.98  ------ Preprocessing Options
% 1.57/0.98  
% 1.57/0.98  --preprocessing_flag                    true
% 1.57/0.98  --time_out_prep_mult                    0.1
% 1.57/0.98  --splitting_mode                        input
% 1.57/0.98  --splitting_grd                         true
% 1.57/0.98  --splitting_cvd                         false
% 1.57/0.98  --splitting_cvd_svl                     false
% 1.57/0.98  --splitting_nvd                         32
% 1.57/0.98  --sub_typing                            true
% 1.57/0.98  --prep_gs_sim                           true
% 1.57/0.98  --prep_unflatten                        true
% 1.57/0.98  --prep_res_sim                          true
% 1.57/0.98  --prep_upred                            true
% 1.57/0.98  --prep_sem_filter                       exhaustive
% 1.57/0.98  --prep_sem_filter_out                   false
% 1.57/0.98  --pred_elim                             true
% 1.57/0.98  --res_sim_input                         true
% 1.57/0.98  --eq_ax_congr_red                       true
% 1.57/0.98  --pure_diseq_elim                       true
% 1.57/0.98  --brand_transform                       false
% 1.57/0.98  --non_eq_to_eq                          false
% 1.57/0.98  --prep_def_merge                        true
% 1.57/0.98  --prep_def_merge_prop_impl              false
% 1.57/0.98  --prep_def_merge_mbd                    true
% 1.57/0.98  --prep_def_merge_tr_red                 false
% 1.57/0.98  --prep_def_merge_tr_cl                  false
% 1.57/0.98  --smt_preprocessing                     true
% 1.57/0.98  --smt_ac_axioms                         fast
% 1.57/0.98  --preprocessed_out                      false
% 1.57/0.98  --preprocessed_stats                    false
% 1.57/0.98  
% 1.57/0.98  ------ Abstraction refinement Options
% 1.57/0.98  
% 1.57/0.98  --abstr_ref                             []
% 1.57/0.98  --abstr_ref_prep                        false
% 1.57/0.98  --abstr_ref_until_sat                   false
% 1.57/0.98  --abstr_ref_sig_restrict                funpre
% 1.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.57/0.98  --abstr_ref_under                       []
% 1.57/0.98  
% 1.57/0.98  ------ SAT Options
% 1.57/0.98  
% 1.57/0.98  --sat_mode                              false
% 1.57/0.98  --sat_fm_restart_options                ""
% 1.57/0.98  --sat_gr_def                            false
% 1.57/0.98  --sat_epr_types                         true
% 1.57/0.98  --sat_non_cyclic_types                  false
% 1.57/0.98  --sat_finite_models                     false
% 1.57/0.98  --sat_fm_lemmas                         false
% 1.57/0.98  --sat_fm_prep                           false
% 1.57/0.98  --sat_fm_uc_incr                        true
% 1.57/0.98  --sat_out_model                         small
% 1.57/0.98  --sat_out_clauses                       false
% 1.57/0.98  
% 1.57/0.98  ------ QBF Options
% 1.57/0.98  
% 1.57/0.98  --qbf_mode                              false
% 1.57/0.98  --qbf_elim_univ                         false
% 1.57/0.98  --qbf_dom_inst                          none
% 1.57/0.98  --qbf_dom_pre_inst                      false
% 1.57/0.98  --qbf_sk_in                             false
% 1.57/0.98  --qbf_pred_elim                         true
% 1.57/0.98  --qbf_split                             512
% 1.57/0.98  
% 1.57/0.98  ------ BMC1 Options
% 1.57/0.98  
% 1.57/0.98  --bmc1_incremental                      false
% 1.57/0.98  --bmc1_axioms                           reachable_all
% 1.57/0.98  --bmc1_min_bound                        0
% 1.57/0.98  --bmc1_max_bound                        -1
% 1.57/0.98  --bmc1_max_bound_default                -1
% 1.57/0.98  --bmc1_symbol_reachability              true
% 1.57/0.98  --bmc1_property_lemmas                  false
% 1.57/0.98  --bmc1_k_induction                      false
% 1.57/0.98  --bmc1_non_equiv_states                 false
% 1.57/0.98  --bmc1_deadlock                         false
% 1.57/0.98  --bmc1_ucm                              false
% 1.57/0.98  --bmc1_add_unsat_core                   none
% 1.57/0.98  --bmc1_unsat_core_children              false
% 1.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.57/0.98  --bmc1_out_stat                         full
% 1.57/0.98  --bmc1_ground_init                      false
% 1.57/0.98  --bmc1_pre_inst_next_state              false
% 1.57/0.98  --bmc1_pre_inst_state                   false
% 1.57/0.98  --bmc1_pre_inst_reach_state             false
% 1.57/0.98  --bmc1_out_unsat_core                   false
% 1.57/0.98  --bmc1_aig_witness_out                  false
% 1.57/0.98  --bmc1_verbose                          false
% 1.57/0.98  --bmc1_dump_clauses_tptp                false
% 1.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.57/0.98  --bmc1_dump_file                        -
% 1.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.57/0.98  --bmc1_ucm_extend_mode                  1
% 1.57/0.98  --bmc1_ucm_init_mode                    2
% 1.57/0.98  --bmc1_ucm_cone_mode                    none
% 1.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.57/0.98  --bmc1_ucm_relax_model                  4
% 1.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.57/0.98  --bmc1_ucm_layered_model                none
% 1.57/0.98  --bmc1_ucm_max_lemma_size               10
% 1.57/0.98  
% 1.57/0.98  ------ AIG Options
% 1.57/0.98  
% 1.57/0.98  --aig_mode                              false
% 1.57/0.98  
% 1.57/0.98  ------ Instantiation Options
% 1.57/0.98  
% 1.57/0.98  --instantiation_flag                    true
% 1.57/0.98  --inst_sos_flag                         false
% 1.57/0.98  --inst_sos_phase                        true
% 1.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.57/0.98  --inst_lit_sel_side                     num_symb
% 1.57/0.98  --inst_solver_per_active                1400
% 1.57/0.98  --inst_solver_calls_frac                1.
% 1.57/0.98  --inst_passive_queue_type               priority_queues
% 1.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.57/0.98  --inst_passive_queues_freq              [25;2]
% 1.57/0.98  --inst_dismatching                      true
% 1.57/0.98  --inst_eager_unprocessed_to_passive     true
% 1.57/0.98  --inst_prop_sim_given                   true
% 1.57/0.98  --inst_prop_sim_new                     false
% 1.57/0.98  --inst_subs_new                         false
% 1.57/0.98  --inst_eq_res_simp                      false
% 1.57/0.98  --inst_subs_given                       false
% 1.57/0.98  --inst_orphan_elimination               true
% 1.57/0.98  --inst_learning_loop_flag               true
% 1.57/0.98  --inst_learning_start                   3000
% 1.57/0.98  --inst_learning_factor                  2
% 1.57/0.98  --inst_start_prop_sim_after_learn       3
% 1.57/0.98  --inst_sel_renew                        solver
% 1.57/0.98  --inst_lit_activity_flag                true
% 1.57/0.98  --inst_restr_to_given                   false
% 1.57/0.98  --inst_activity_threshold               500
% 1.57/0.98  --inst_out_proof                        true
% 1.57/0.98  
% 1.57/0.98  ------ Resolution Options
% 1.57/0.98  
% 1.57/0.98  --resolution_flag                       true
% 1.57/0.98  --res_lit_sel                           adaptive
% 1.57/0.98  --res_lit_sel_side                      none
% 1.57/0.98  --res_ordering                          kbo
% 1.57/0.98  --res_to_prop_solver                    active
% 1.57/0.98  --res_prop_simpl_new                    false
% 1.57/0.98  --res_prop_simpl_given                  true
% 1.57/0.98  --res_passive_queue_type                priority_queues
% 1.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.57/0.98  --res_passive_queues_freq               [15;5]
% 1.57/0.98  --res_forward_subs                      full
% 1.57/0.98  --res_backward_subs                     full
% 1.57/0.98  --res_forward_subs_resolution           true
% 1.57/0.98  --res_backward_subs_resolution          true
% 1.57/0.98  --res_orphan_elimination                true
% 1.57/0.98  --res_time_limit                        2.
% 1.57/0.98  --res_out_proof                         true
% 1.57/0.98  
% 1.57/0.98  ------ Superposition Options
% 1.57/0.98  
% 1.57/0.98  --superposition_flag                    true
% 1.57/0.98  --sup_passive_queue_type                priority_queues
% 1.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.57/0.98  --demod_completeness_check              fast
% 1.57/0.98  --demod_use_ground                      true
% 1.57/0.98  --sup_to_prop_solver                    passive
% 1.57/0.98  --sup_prop_simpl_new                    true
% 1.57/0.98  --sup_prop_simpl_given                  true
% 1.57/0.98  --sup_fun_splitting                     false
% 1.57/0.98  --sup_smt_interval                      50000
% 1.57/0.98  
% 1.57/0.98  ------ Superposition Simplification Setup
% 1.57/0.98  
% 1.57/0.98  --sup_indices_passive                   []
% 1.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/0.98  --sup_full_bw                           [BwDemod]
% 1.57/0.98  --sup_immed_triv                        [TrivRules]
% 1.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/0.98  --sup_immed_bw_main                     []
% 1.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.57/0.98  
% 1.57/0.98  ------ Combination Options
% 1.57/0.98  
% 1.57/0.98  --comb_res_mult                         3
% 1.57/0.98  --comb_sup_mult                         2
% 1.57/0.98  --comb_inst_mult                        10
% 1.57/0.98  
% 1.57/0.98  ------ Debug Options
% 1.57/0.98  
% 1.57/0.98  --dbg_backtrace                         false
% 1.57/0.98  --dbg_dump_prop_clauses                 false
% 1.57/0.98  --dbg_dump_prop_clauses_file            -
% 1.57/0.98  --dbg_out_stat                          false
% 1.57/0.98  ------ Parsing...
% 1.57/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.57/0.98  
% 1.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.57/0.98  
% 1.57/0.98  ------ Preprocessing... gs_s  sp: 5 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.57/0.98  
% 1.57/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.57/0.98  ------ Proving...
% 1.57/0.98  ------ Problem Properties 
% 1.57/0.98  
% 1.57/0.98  
% 1.57/0.98  clauses                                 22
% 1.57/0.98  conjectures                             5
% 1.57/0.98  EPR                                     5
% 1.57/0.98  Horn                                    15
% 1.57/0.98  unary                                   2
% 1.57/0.98  binary                                  11
% 1.57/0.98  lits                                    57
% 1.57/0.98  lits eq                                 3
% 1.57/0.98  fd_pure                                 0
% 1.57/0.98  fd_pseudo                               0
% 1.57/0.98  fd_cond                                 0
% 1.57/0.98  fd_pseudo_cond                          0
% 1.57/0.98  AC symbols                              0
% 1.57/0.98  
% 1.57/0.98  ------ Schedule dynamic 5 is on 
% 1.57/0.98  
% 1.57/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.57/0.98  
% 1.57/0.98  
% 1.57/0.98  ------ 
% 1.57/0.98  Current options:
% 1.57/0.98  ------ 
% 1.57/0.98  
% 1.57/0.98  ------ Input Options
% 1.57/0.98  
% 1.57/0.98  --out_options                           all
% 1.57/0.98  --tptp_safe_out                         true
% 1.57/0.98  --problem_path                          ""
% 1.57/0.98  --include_path                          ""
% 1.57/0.98  --clausifier                            res/vclausify_rel
% 1.57/0.98  --clausifier_options                    --mode clausify
% 1.57/0.98  --stdin                                 false
% 1.57/0.98  --stats_out                             all
% 1.57/0.98  
% 1.57/0.98  ------ General Options
% 1.57/0.98  
% 1.57/0.98  --fof                                   false
% 1.57/0.98  --time_out_real                         305.
% 1.57/0.98  --time_out_virtual                      -1.
% 1.57/0.98  --symbol_type_check                     false
% 1.57/0.98  --clausify_out                          false
% 1.57/0.98  --sig_cnt_out                           false
% 1.57/0.98  --trig_cnt_out                          false
% 1.57/0.98  --trig_cnt_out_tolerance                1.
% 1.57/0.98  --trig_cnt_out_sk_spl                   false
% 1.57/0.98  --abstr_cl_out                          false
% 1.57/0.98  
% 1.57/0.98  ------ Global Options
% 1.57/0.98  
% 1.57/0.98  --schedule                              default
% 1.57/0.98  --add_important_lit                     false
% 1.57/0.98  --prop_solver_per_cl                    1000
% 1.57/0.98  --min_unsat_core                        false
% 1.57/0.98  --soft_assumptions                      false
% 1.57/0.98  --soft_lemma_size                       3
% 1.57/0.98  --prop_impl_unit_size                   0
% 1.57/0.98  --prop_impl_unit                        []
% 1.57/0.98  --share_sel_clauses                     true
% 1.57/0.98  --reset_solvers                         false
% 1.57/0.98  --bc_imp_inh                            [conj_cone]
% 1.57/0.98  --conj_cone_tolerance                   3.
% 1.57/0.98  --extra_neg_conj                        none
% 1.57/0.98  --large_theory_mode                     true
% 1.57/0.98  --prolific_symb_bound                   200
% 1.57/0.98  --lt_threshold                          2000
% 1.57/0.98  --clause_weak_htbl                      true
% 1.57/0.98  --gc_record_bc_elim                     false
% 1.57/0.98  
% 1.57/0.98  ------ Preprocessing Options
% 1.57/0.98  
% 1.57/0.98  --preprocessing_flag                    true
% 1.57/0.98  --time_out_prep_mult                    0.1
% 1.57/0.98  --splitting_mode                        input
% 1.57/0.98  --splitting_grd                         true
% 1.57/0.98  --splitting_cvd                         false
% 1.57/0.98  --splitting_cvd_svl                     false
% 1.57/0.98  --splitting_nvd                         32
% 1.57/0.98  --sub_typing                            true
% 1.57/0.98  --prep_gs_sim                           true
% 1.57/0.98  --prep_unflatten                        true
% 1.57/0.98  --prep_res_sim                          true
% 1.57/0.98  --prep_upred                            true
% 1.57/0.98  --prep_sem_filter                       exhaustive
% 1.57/0.98  --prep_sem_filter_out                   false
% 1.57/0.98  --pred_elim                             true
% 1.57/0.98  --res_sim_input                         true
% 1.57/0.98  --eq_ax_congr_red                       true
% 1.57/0.98  --pure_diseq_elim                       true
% 1.57/0.98  --brand_transform                       false
% 1.57/0.98  --non_eq_to_eq                          false
% 1.57/0.98  --prep_def_merge                        true
% 1.57/0.98  --prep_def_merge_prop_impl              false
% 1.57/0.98  --prep_def_merge_mbd                    true
% 1.57/0.98  --prep_def_merge_tr_red                 false
% 1.57/0.98  --prep_def_merge_tr_cl                  false
% 1.57/0.98  --smt_preprocessing                     true
% 1.57/0.98  --smt_ac_axioms                         fast
% 1.57/0.98  --preprocessed_out                      false
% 1.57/0.98  --preprocessed_stats                    false
% 1.57/0.98  
% 1.57/0.98  ------ Abstraction refinement Options
% 1.57/0.98  
% 1.57/0.98  --abstr_ref                             []
% 1.57/0.98  --abstr_ref_prep                        false
% 1.57/0.98  --abstr_ref_until_sat                   false
% 1.57/0.98  --abstr_ref_sig_restrict                funpre
% 1.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.57/0.98  --abstr_ref_under                       []
% 1.57/0.98  
% 1.57/0.98  ------ SAT Options
% 1.57/0.98  
% 1.57/0.98  --sat_mode                              false
% 1.57/0.98  --sat_fm_restart_options                ""
% 1.57/0.98  --sat_gr_def                            false
% 1.57/0.98  --sat_epr_types                         true
% 1.57/0.98  --sat_non_cyclic_types                  false
% 1.57/0.98  --sat_finite_models                     false
% 1.57/0.98  --sat_fm_lemmas                         false
% 1.57/0.98  --sat_fm_prep                           false
% 1.57/0.98  --sat_fm_uc_incr                        true
% 1.57/0.98  --sat_out_model                         small
% 1.57/0.98  --sat_out_clauses                       false
% 1.57/0.98  
% 1.57/0.98  ------ QBF Options
% 1.57/0.98  
% 1.57/0.98  --qbf_mode                              false
% 1.57/0.98  --qbf_elim_univ                         false
% 1.57/0.98  --qbf_dom_inst                          none
% 1.57/0.98  --qbf_dom_pre_inst                      false
% 1.57/0.98  --qbf_sk_in                             false
% 1.57/0.98  --qbf_pred_elim                         true
% 1.57/0.98  --qbf_split                             512
% 1.57/0.98  
% 1.57/0.98  ------ BMC1 Options
% 1.57/0.98  
% 1.57/0.98  --bmc1_incremental                      false
% 1.57/0.98  --bmc1_axioms                           reachable_all
% 1.57/0.98  --bmc1_min_bound                        0
% 1.57/0.98  --bmc1_max_bound                        -1
% 1.57/0.98  --bmc1_max_bound_default                -1
% 1.57/0.98  --bmc1_symbol_reachability              true
% 1.57/0.98  --bmc1_property_lemmas                  false
% 1.57/0.98  --bmc1_k_induction                      false
% 1.57/0.98  --bmc1_non_equiv_states                 false
% 1.57/0.98  --bmc1_deadlock                         false
% 1.57/0.98  --bmc1_ucm                              false
% 1.57/0.98  --bmc1_add_unsat_core                   none
% 1.57/0.98  --bmc1_unsat_core_children              false
% 1.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.57/0.98  --bmc1_out_stat                         full
% 1.57/0.98  --bmc1_ground_init                      false
% 1.57/0.98  --bmc1_pre_inst_next_state              false
% 1.57/0.98  --bmc1_pre_inst_state                   false
% 1.57/0.98  --bmc1_pre_inst_reach_state             false
% 1.57/0.98  --bmc1_out_unsat_core                   false
% 1.57/0.98  --bmc1_aig_witness_out                  false
% 1.57/0.98  --bmc1_verbose                          false
% 1.57/0.98  --bmc1_dump_clauses_tptp                false
% 1.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.57/0.98  --bmc1_dump_file                        -
% 1.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.57/0.98  --bmc1_ucm_extend_mode                  1
% 1.57/0.98  --bmc1_ucm_init_mode                    2
% 1.57/0.98  --bmc1_ucm_cone_mode                    none
% 1.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.57/0.98  --bmc1_ucm_relax_model                  4
% 1.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.57/0.98  --bmc1_ucm_layered_model                none
% 1.57/0.98  --bmc1_ucm_max_lemma_size               10
% 1.57/0.98  
% 1.57/0.98  ------ AIG Options
% 1.57/0.98  
% 1.57/0.98  --aig_mode                              false
% 1.57/0.98  
% 1.57/0.98  ------ Instantiation Options
% 1.57/0.98  
% 1.57/0.98  --instantiation_flag                    true
% 1.57/0.98  --inst_sos_flag                         false
% 1.57/0.98  --inst_sos_phase                        true
% 1.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.57/0.98  --inst_lit_sel_side                     none
% 1.57/0.98  --inst_solver_per_active                1400
% 1.57/0.98  --inst_solver_calls_frac                1.
% 1.57/0.98  --inst_passive_queue_type               priority_queues
% 1.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.57/0.98  --inst_passive_queues_freq              [25;2]
% 1.57/0.98  --inst_dismatching                      true
% 1.57/0.98  --inst_eager_unprocessed_to_passive     true
% 1.57/0.98  --inst_prop_sim_given                   true
% 1.57/0.98  --inst_prop_sim_new                     false
% 1.57/0.98  --inst_subs_new                         false
% 1.57/0.98  --inst_eq_res_simp                      false
% 1.57/0.98  --inst_subs_given                       false
% 1.57/0.98  --inst_orphan_elimination               true
% 1.57/0.98  --inst_learning_loop_flag               true
% 1.57/0.98  --inst_learning_start                   3000
% 1.57/0.98  --inst_learning_factor                  2
% 1.57/0.98  --inst_start_prop_sim_after_learn       3
% 1.57/0.98  --inst_sel_renew                        solver
% 1.57/0.98  --inst_lit_activity_flag                true
% 1.57/0.98  --inst_restr_to_given                   false
% 1.57/0.98  --inst_activity_threshold               500
% 1.57/0.98  --inst_out_proof                        true
% 1.57/0.98  
% 1.57/0.98  ------ Resolution Options
% 1.57/0.98  
% 1.57/0.98  --resolution_flag                       false
% 1.57/0.98  --res_lit_sel                           adaptive
% 1.57/0.98  --res_lit_sel_side                      none
% 1.57/0.98  --res_ordering                          kbo
% 1.57/0.98  --res_to_prop_solver                    active
% 1.57/0.98  --res_prop_simpl_new                    false
% 1.57/0.98  --res_prop_simpl_given                  true
% 1.57/0.98  --res_passive_queue_type                priority_queues
% 1.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.57/0.98  --res_passive_queues_freq               [15;5]
% 1.57/0.98  --res_forward_subs                      full
% 1.57/0.98  --res_backward_subs                     full
% 1.57/0.98  --res_forward_subs_resolution           true
% 1.57/0.98  --res_backward_subs_resolution          true
% 1.57/0.98  --res_orphan_elimination                true
% 1.57/0.98  --res_time_limit                        2.
% 1.57/0.98  --res_out_proof                         true
% 1.57/0.98  
% 1.57/0.98  ------ Superposition Options
% 1.57/0.98  
% 1.57/0.98  --superposition_flag                    true
% 1.57/0.98  --sup_passive_queue_type                priority_queues
% 1.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.57/0.98  --demod_completeness_check              fast
% 1.57/0.98  --demod_use_ground                      true
% 1.57/0.98  --sup_to_prop_solver                    passive
% 1.57/0.98  --sup_prop_simpl_new                    true
% 1.57/0.98  --sup_prop_simpl_given                  true
% 1.57/0.98  --sup_fun_splitting                     false
% 1.57/0.98  --sup_smt_interval                      50000
% 1.57/0.98  
% 1.57/0.98  ------ Superposition Simplification Setup
% 1.57/0.98  
% 1.57/0.98  --sup_indices_passive                   []
% 1.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/0.98  --sup_full_bw                           [BwDemod]
% 1.57/0.98  --sup_immed_triv                        [TrivRules]
% 1.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/0.98  --sup_immed_bw_main                     []
% 1.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.57/0.98  
% 1.57/0.98  ------ Combination Options
% 1.57/0.98  
% 1.57/0.98  --comb_res_mult                         3
% 1.57/0.98  --comb_sup_mult                         2
% 1.57/0.98  --comb_inst_mult                        10
% 1.57/0.98  
% 1.57/0.98  ------ Debug Options
% 1.57/0.98  
% 1.57/0.98  --dbg_backtrace                         false
% 1.57/0.98  --dbg_dump_prop_clauses                 false
% 1.57/0.98  --dbg_dump_prop_clauses_file            -
% 1.57/0.98  --dbg_out_stat                          false
% 1.57/0.98  
% 1.57/0.98  
% 1.57/0.98  
% 1.57/0.98  
% 1.57/0.98  ------ Proving...
% 1.57/0.98  
% 1.57/0.98  
% 1.57/0.98  % SZS status Theorem for theBenchmark.p
% 1.57/0.98  
% 1.57/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.57/0.98  
% 1.57/0.98  fof(f1,axiom,(
% 1.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/0.98  
% 1.57/0.98  fof(f10,plain,(
% 1.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.98    inference(ennf_transformation,[],[f1])).
% 1.57/0.98  
% 1.57/0.98  fof(f24,plain,(
% 1.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.98    inference(nnf_transformation,[],[f10])).
% 1.57/0.98  
% 1.57/0.98  fof(f25,plain,(
% 1.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.98    inference(rectify,[],[f24])).
% 1.57/0.98  
% 1.57/0.98  fof(f26,plain,(
% 1.57/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.57/0.98    introduced(choice_axiom,[])).
% 1.57/0.98  
% 1.57/0.98  fof(f27,plain,(
% 1.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.57/0.98  
% 1.57/0.98  fof(f37,plain,(
% 1.57/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f27])).
% 1.57/0.98  
% 1.57/0.98  fof(f8,conjecture,(
% 1.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/0.98  
% 1.57/0.98  fof(f9,negated_conjecture,(
% 1.57/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.57/0.98    inference(negated_conjecture,[],[f8])).
% 1.57/0.98  
% 1.57/0.98  fof(f22,plain,(
% 1.57/0.98    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.57/0.98    inference(ennf_transformation,[],[f9])).
% 1.57/0.98  
% 1.57/0.98  fof(f23,plain,(
% 1.57/0.98    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.98    inference(flattening,[],[f22])).
% 1.57/0.98  
% 1.57/0.98  fof(f29,plain,(
% 1.57/0.98    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.98    inference(nnf_transformation,[],[f23])).
% 1.57/0.98  
% 1.57/0.98  fof(f30,plain,(
% 1.57/0.98    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.98    inference(flattening,[],[f29])).
% 1.57/0.98  
% 1.57/0.98  fof(f31,plain,(
% 1.57/0.98    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.98    inference(rectify,[],[f30])).
% 1.57/0.98  
% 1.57/0.98  fof(f35,plain,(
% 1.57/0.98    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4) & r1_tarski(sK4,X2) & v3_pre_topc(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.57/0.98    introduced(choice_axiom,[])).
% 1.57/0.98  
% 1.57/0.98  fof(f34,plain,(
% 1.57/0.98    ( ! [X0,X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(sK3,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,sK3) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(sK3,X0,X1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.57/0.98    introduced(choice_axiom,[])).
% 1.57/0.98  
% 1.57/0.98  fof(f33,plain,(
% 1.57/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,sK2)) & (? [X4] : (r2_hidden(sK2,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,sK2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.57/0.98    introduced(choice_axiom,[])).
% 1.57/0.98  
% 1.57/0.98  fof(f32,plain,(
% 1.57/0.98    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~m1_connsp_2(X2,sK1,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_connsp_2(X2,sK1,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.57/0.98    introduced(choice_axiom,[])).
% 1.57/0.98  
% 1.57/0.98  fof(f36,plain,(
% 1.57/0.98    (((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~m1_connsp_2(sK3,sK1,sK2)) & ((r2_hidden(sK2,sK4) & r1_tarski(sK4,sK3) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_connsp_2(sK3,sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f35,f34,f33,f32])).
% 1.57/0.98  
% 1.57/0.98  fof(f52,plain,(
% 1.57/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f7,axiom,(
% 1.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/0.98  
% 1.57/0.98  fof(f20,plain,(
% 1.57/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.98    inference(ennf_transformation,[],[f7])).
% 1.57/0.98  
% 1.57/0.98  fof(f21,plain,(
% 1.57/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.98    inference(flattening,[],[f20])).
% 1.57/0.98  
% 1.57/0.98  fof(f28,plain,(
% 1.57/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.98    inference(nnf_transformation,[],[f21])).
% 1.57/0.98  
% 1.57/0.98  fof(f46,plain,(
% 1.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f28])).
% 1.57/0.98  
% 1.57/0.98  fof(f48,plain,(
% 1.57/0.98    ~v2_struct_0(sK1)),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f49,plain,(
% 1.57/0.98    v2_pre_topc(sK1)),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f50,plain,(
% 1.57/0.98    l1_pre_topc(sK1)),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f5,axiom,(
% 1.57/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/0.98  
% 1.57/0.98  fof(f16,plain,(
% 1.57/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.98    inference(ennf_transformation,[],[f5])).
% 1.57/0.98  
% 1.57/0.98  fof(f17,plain,(
% 1.57/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.98    inference(flattening,[],[f16])).
% 1.57/0.98  
% 1.57/0.98  fof(f43,plain,(
% 1.57/0.98    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f17])).
% 1.57/0.98  
% 1.57/0.98  fof(f53,plain,(
% 1.57/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | m1_connsp_2(sK3,sK1,sK2)),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f51,plain,(
% 1.57/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f57,plain,(
% 1.57/0.98    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(sK3,sK1,sK2)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f3,axiom,(
% 1.57/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/0.98  
% 1.57/0.98  fof(f13,plain,(
% 1.57/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.57/0.98    inference(ennf_transformation,[],[f3])).
% 1.57/0.98  
% 1.57/0.98  fof(f14,plain,(
% 1.57/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.57/0.98    inference(flattening,[],[f13])).
% 1.57/0.98  
% 1.57/0.98  fof(f41,plain,(
% 1.57/0.98    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f14])).
% 1.57/0.98  
% 1.57/0.98  fof(f2,axiom,(
% 1.57/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/0.98  
% 1.57/0.98  fof(f11,plain,(
% 1.57/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.57/0.98    inference(ennf_transformation,[],[f2])).
% 1.57/0.98  
% 1.57/0.98  fof(f12,plain,(
% 1.57/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.57/0.98    inference(flattening,[],[f11])).
% 1.57/0.98  
% 1.57/0.98  fof(f40,plain,(
% 1.57/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f12])).
% 1.57/0.98  
% 1.57/0.98  fof(f4,axiom,(
% 1.57/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/0.98  
% 1.57/0.98  fof(f15,plain,(
% 1.57/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.98    inference(ennf_transformation,[],[f4])).
% 1.57/0.98  
% 1.57/0.98  fof(f42,plain,(
% 1.57/0.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f15])).
% 1.57/0.98  
% 1.57/0.98  fof(f55,plain,(
% 1.57/0.98    r1_tarski(sK4,sK3) | m1_connsp_2(sK3,sK1,sK2)),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f56,plain,(
% 1.57/0.98    r2_hidden(sK2,sK4) | m1_connsp_2(sK3,sK1,sK2)),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  fof(f47,plain,(
% 1.57/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f28])).
% 1.57/0.98  
% 1.57/0.98  fof(f6,axiom,(
% 1.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/0.98  
% 1.57/0.98  fof(f18,plain,(
% 1.57/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.57/0.98    inference(ennf_transformation,[],[f6])).
% 1.57/0.98  
% 1.57/0.98  fof(f19,plain,(
% 1.57/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.57/0.98    inference(flattening,[],[f18])).
% 1.57/0.98  
% 1.57/0.98  fof(f45,plain,(
% 1.57/0.98    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f19])).
% 1.57/0.98  
% 1.57/0.98  fof(f44,plain,(
% 1.57/0.98    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.57/0.98    inference(cnf_transformation,[],[f19])).
% 1.57/0.98  
% 1.57/0.98  fof(f54,plain,(
% 1.57/0.98    v3_pre_topc(sK4,sK1) | m1_connsp_2(sK3,sK1,sK2)),
% 1.57/0.98    inference(cnf_transformation,[],[f36])).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2,plain,
% 1.57/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.57/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1376,plain,
% 1.57/0.98      ( ~ r2_hidden(X0_44,X1_44)
% 1.57/0.98      | r2_hidden(X0_44,X2_44)
% 1.57/0.98      | ~ r1_tarski(X1_44,X2_44) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2266,plain,
% 1.57/0.98      ( ~ r2_hidden(X0_44,X1_44)
% 1.57/0.98      | r2_hidden(X0_44,k1_tops_1(sK1,sK3))
% 1.57/0.98      | ~ r1_tarski(X1_44,k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1376]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2948,plain,
% 1.57/0.98      ( ~ r2_hidden(X0_44,k1_tops_1(sK1,sK4))
% 1.57/0.98      | r2_hidden(X0_44,k1_tops_1(sK1,sK3))
% 1.57/0.98      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_2266]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2950,plain,
% 1.57/0.98      ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 1.57/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 1.57/0.98      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_2948]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_16,negated_conjecture,
% 1.57/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1372,negated_conjecture,
% 1.57/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1783,plain,
% 1.57/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1372]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_10,plain,
% 1.57/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.57/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.57/0.98      | v2_struct_0(X1)
% 1.57/0.98      | ~ v2_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(X1) ),
% 1.57/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_20,negated_conjecture,
% 1.57/0.98      ( ~ v2_struct_0(sK1) ),
% 1.57/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_230,plain,
% 1.57/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.57/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.57/0.98      | ~ v2_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(X1)
% 1.57/0.98      | sK1 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_231,plain,
% 1.57/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 1.57/0.98      | ~ v2_pre_topc(sK1)
% 1.57/0.98      | ~ l1_pre_topc(sK1) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_230]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_19,negated_conjecture,
% 1.57/0.98      ( v2_pre_topc(sK1) ),
% 1.57/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_18,negated_conjecture,
% 1.57/0.98      ( l1_pre_topc(sK1) ),
% 1.57/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_235,plain,
% 1.57/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_231,c_19,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1370,plain,
% 1.57/0.98      ( ~ m1_connsp_2(X0_44,sK1,X1_44)
% 1.57/0.98      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_235]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1785,plain,
% 1.57/0.98      ( m1_connsp_2(X0_44,sK1,X1_44) != iProver_top
% 1.57/0.98      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.57/0.98      | m1_subset_1(X1_44,u1_struct_0(sK1)) != iProver_top
% 1.57/0.98      | r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1370]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2559,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,X0_44) != iProver_top
% 1.57/0.98      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 1.57/0.98      | r2_hidden(X0_44,k1_tops_1(sK1,sK3)) = iProver_top ),
% 1.57/0.98      inference(superposition,[status(thm)],[c_1783,c_1785]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2584,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,X0_44)
% 1.57/0.98      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(X0_44,k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2559]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2586,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_2584]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1389,plain,
% 1.57/0.98      ( ~ r2_hidden(X0_44,X1_44)
% 1.57/0.98      | r2_hidden(X2_44,X3_44)
% 1.57/0.98      | X2_44 != X0_44
% 1.57/0.98      | X3_44 != X1_44 ),
% 1.57/0.98      theory(equality) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2007,plain,
% 1.57/0.98      ( r2_hidden(X0_44,X1_44)
% 1.57/0.98      | ~ r2_hidden(sK2,sK4)
% 1.57/0.98      | X1_44 != sK4
% 1.57/0.98      | X0_44 != sK2 ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1389]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2251,plain,
% 1.57/0.98      ( r2_hidden(X0_44,k1_tops_1(sK1,sK4))
% 1.57/0.98      | ~ r2_hidden(sK2,sK4)
% 1.57/0.98      | X0_44 != sK2
% 1.57/0.98      | k1_tops_1(sK1,sK4) != sK4 ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_2007]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2253,plain,
% 1.57/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 1.57/0.98      | ~ r2_hidden(sK2,sK4)
% 1.57/0.98      | k1_tops_1(sK1,sK4) != sK4
% 1.57/0.98      | sK2 != sK2 ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_2251]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_6,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ r1_tarski(X0,X2)
% 1.57/0.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 1.57/0.98      | ~ l1_pre_topc(X1) ),
% 1.57/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_389,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ r1_tarski(X0,X2)
% 1.57/0.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 1.57/0.98      | sK1 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_390,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r1_tarski(X1,X0)
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_389]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1368,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r1_tarski(X1_44,X0_44)
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,X1_44),k1_tops_1(sK1,X0_44)) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_390]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1964,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r1_tarski(X0_44,sK3)
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,X0_44),k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1368]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2197,plain,
% 1.57/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,sK3))
% 1.57/0.98      | ~ r1_tarski(sK4,sK3) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1964]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_15,negated_conjecture,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1373,negated_conjecture,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1782,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
% 1.57/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1373]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_25,plain,
% 1.57/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_26,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
% 1.57/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_769,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.57/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 1.57/0.98      | sK1 != sK1
% 1.57/0.98      | sK3 != X0
% 1.57/0.98      | sK2 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_235]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_770,plain,
% 1.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_769]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_17,negated_conjecture,
% 1.57/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.57/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_772,plain,
% 1.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_770,c_17,c_16]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_774,plain,
% 1.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.57/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_11,negated_conjecture,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ v3_pre_topc(X0,sK1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(sK2,X0)
% 1.57/0.98      | ~ r1_tarski(X0,sK3) ),
% 1.57/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_4,plain,
% 1.57/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.57/0.98      | ~ v2_pre_topc(X0)
% 1.57/0.98      | ~ l1_pre_topc(X0) ),
% 1.57/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_288,plain,
% 1.57/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.57/0.98      | ~ l1_pre_topc(X0)
% 1.57/0.98      | sK1 != X0 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_289,plain,
% 1.57/0.98      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ l1_pre_topc(sK1) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_288]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_293,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_289,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_294,plain,
% 1.57/0.98      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/0.98      inference(renaming,[status(thm)],[c_293]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_537,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(sK2,X0)
% 1.57/0.98      | ~ r1_tarski(X0,sK3)
% 1.57/0.98      | k1_tops_1(sK1,X1) != X0
% 1.57/0.98      | sK1 != sK1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_294]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_538,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 1.57/0.98      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_537]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_3,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ l1_pre_topc(X1) ),
% 1.57/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_419,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | sK1 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_420,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_419]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_542,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 1.57/0.98      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_538,c_420]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_543,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 1.57/0.98      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3) ),
% 1.57/0.98      inference(renaming,[status(thm)],[c_542]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1362,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0_44))
% 1.57/0.98      | ~ r1_tarski(k1_tops_1(sK1,X0_44),sK3) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_543]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1954,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 1.57/0.98      | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1362]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1955,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
% 1.57/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.57/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1954]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_5,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.57/0.98      | ~ l1_pre_topc(X1) ),
% 1.57/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_407,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.57/0.98      | sK1 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_408,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_407]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1367,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,X0_44),X0_44) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_408]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1961,plain,
% 1.57/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1367]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1962,plain,
% 1.57/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.57/0.98      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1961]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2036,plain,
% 1.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_1782,c_25,c_26,c_774,c_1955,c_1962]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2038,plain,
% 1.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2036]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_13,negated_conjecture,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) | r1_tarski(sK4,sK3) ),
% 1.57/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1374,negated_conjecture,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) | r1_tarski(sK4,sK3) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1781,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
% 1.57/0.98      | r1_tarski(sK4,sK3) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1374]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_28,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
% 1.57/0.98      | r1_tarski(sK4,sK3) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_783,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 1.57/0.98      | r1_tarski(sK4,sK3)
% 1.57/0.98      | sK1 != sK1
% 1.57/0.98      | sK3 != X0
% 1.57/0.98      | sK2 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_235]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_784,plain,
% 1.57/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 1.57/0.98      | r1_tarski(sK4,sK3) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_783]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_786,plain,
% 1.57/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r1_tarski(sK4,sK3) ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_784,c_17,c_16]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_788,plain,
% 1.57/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 1.57/0.98      | r1_tarski(sK4,sK3) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2002,plain,
% 1.57/0.98      ( r1_tarski(sK4,sK3) = iProver_top ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_1781,c_25,c_28,c_788,c_1955,c_1962]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_2004,plain,
% 1.57/0.98      ( r1_tarski(sK4,sK3) ),
% 1.57/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2002]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_12,negated_conjecture,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) | r2_hidden(sK2,sK4) ),
% 1.57/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1375,negated_conjecture,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) | r2_hidden(sK2,sK4) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1780,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
% 1.57/0.98      | r2_hidden(sK2,sK4) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_29,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
% 1.57/0.98      | r2_hidden(sK2,sK4) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_797,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 1.57/0.98      | r2_hidden(sK2,sK4)
% 1.57/0.98      | sK1 != sK1
% 1.57/0.98      | sK3 != X0
% 1.57/0.98      | sK2 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_235]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_798,plain,
% 1.57/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.57/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 1.57/0.98      | r2_hidden(sK2,sK4) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_797]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_800,plain,
% 1.57/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r2_hidden(sK2,sK4) ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_798,c_17,c_16]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_802,plain,
% 1.57/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 1.57/0.98      | r2_hidden(sK2,sK4) = iProver_top ),
% 1.57/0.98      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1996,plain,
% 1.57/0.98      ( r2_hidden(sK2,sK4) = iProver_top ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_1780,c_25,c_29,c_802,c_1955,c_1962]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1998,plain,
% 1.57/0.98      ( r2_hidden(sK2,sK4) ),
% 1.57/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1996]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_9,plain,
% 1.57/0.98      ( m1_connsp_2(X0,X1,X2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.57/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.57/0.98      | v2_struct_0(X1)
% 1.57/0.98      | ~ v2_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(X1) ),
% 1.57/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_254,plain,
% 1.57/0.98      ( m1_connsp_2(X0,X1,X2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.57/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.57/0.98      | ~ v2_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(X1)
% 1.57/0.98      | sK1 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_255,plain,
% 1.57/0.98      ( m1_connsp_2(X0,sK1,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.57/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 1.57/0.98      | ~ v2_pre_topc(sK1)
% 1.57/0.98      | ~ l1_pre_topc(sK1) ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_254]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_259,plain,
% 1.57/0.98      ( m1_connsp_2(X0,sK1,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.57/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_255,c_19,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1369,plain,
% 1.57/0.98      ( m1_connsp_2(X0_44,sK1,X1_44)
% 1.57/0.98      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 1.57/0.98      | ~ r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_259]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1969,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,X0_44)
% 1.57/0.98      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.57/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(X0_44,k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1369]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1971,plain,
% 1.57/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.57/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1969]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_7,plain,
% 1.57/0.98      ( v3_pre_topc(X0,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.57/0.98      | ~ v2_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(X3)
% 1.57/0.98      | k1_tops_1(X1,X0) != X0 ),
% 1.57/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_306,plain,
% 1.57/0.98      ( v3_pre_topc(X0,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.57/0.98      | ~ l1_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(X3)
% 1.57/0.98      | k1_tops_1(X1,X0) != X0
% 1.57/0.98      | sK1 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_307,plain,
% 1.57/0.98      ( v3_pre_topc(X0,sK1)
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ l1_pre_topc(X2)
% 1.57/0.98      | ~ l1_pre_topc(sK1)
% 1.57/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_306]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_311,plain,
% 1.57/0.98      ( ~ l1_pre_topc(X2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.57/0.98      | v3_pre_topc(X0,sK1)
% 1.57/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_307,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_312,plain,
% 1.57/0.98      ( v3_pre_topc(X0,sK1)
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ l1_pre_topc(X2)
% 1.57/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 1.57/0.98      inference(renaming,[status(thm)],[c_311]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_431,plain,
% 1.57/0.98      ( v3_pre_topc(X0,sK1)
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | k1_tops_1(sK1,X0) != X0
% 1.57/0.98      | sK1 != X2 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_312]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_432,plain,
% 1.57/0.98      ( v3_pre_topc(X0,sK1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_431]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_471,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(sK2,X0)
% 1.57/0.98      | ~ r1_tarski(X0,sK3)
% 1.57/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 1.57/0.98      inference(resolution,[status(thm)],[c_432,c_11]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1365,plain,
% 1.57/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.98      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ r2_hidden(sK2,X0_44)
% 1.57/0.98      | ~ r1_tarski(X0_44,sK3)
% 1.57/0.98      | k1_tops_1(sK1,X0_44) != X0_44 ),
% 1.57/0.98      inference(subtyping,[status(esa)],[c_471]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1379,plain,
% 1.57/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ sP0_iProver_split ),
% 1.57/0.98      inference(splitting,
% 1.57/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.57/0.98                [c_1365]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_1948,plain,
% 1.57/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ sP0_iProver_split ),
% 1.57/0.98      inference(instantiation,[status(thm)],[c_1379]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_8,plain,
% 1.57/0.98      ( ~ v3_pre_topc(X0,X1)
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ v2_pre_topc(X3)
% 1.57/0.98      | ~ l1_pre_topc(X3)
% 1.57/0.98      | ~ l1_pre_topc(X1)
% 1.57/0.98      | k1_tops_1(X1,X0) = X0 ),
% 1.57/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_331,plain,
% 1.57/0.98      ( ~ v3_pre_topc(X0,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.57/0.98      | ~ l1_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(X3)
% 1.57/0.98      | k1_tops_1(X1,X0) = X0
% 1.57/0.98      | sK1 != X3 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_332,plain,
% 1.57/0.98      ( ~ v3_pre_topc(X0,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ l1_pre_topc(X1)
% 1.57/0.98      | ~ l1_pre_topc(sK1)
% 1.57/0.98      | k1_tops_1(X1,X0) = X0 ),
% 1.57/0.98      inference(unflattening,[status(thm)],[c_331]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_336,plain,
% 1.57/0.98      ( ~ l1_pre_topc(X1)
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ v3_pre_topc(X0,X1)
% 1.57/0.98      | k1_tops_1(X1,X0) = X0 ),
% 1.57/0.98      inference(global_propositional_subsumption,
% 1.57/0.98                [status(thm)],
% 1.57/0.98                [c_332,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_337,plain,
% 1.57/0.98      ( ~ v3_pre_topc(X0,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ l1_pre_topc(X1)
% 1.57/0.98      | k1_tops_1(X1,X0) = X0 ),
% 1.57/0.98      inference(renaming,[status(thm)],[c_336]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_371,plain,
% 1.57/0.98      ( ~ v3_pre_topc(X0,X1)
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | k1_tops_1(X1,X0) = X0
% 1.57/0.98      | sK1 != X1 ),
% 1.57/0.98      inference(resolution_lifted,[status(thm)],[c_337,c_18]) ).
% 1.57/0.98  
% 1.57/0.98  cnf(c_372,plain,
% 1.57/0.98      ( ~ v3_pre_topc(X0,sK1)
% 1.57/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.98      | k1_tops_1(sK1,X0) = X0 ),
% 1.57/0.99      inference(unflattening,[status(thm)],[c_371]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_14,negated_conjecture,
% 1.57/0.99      ( m1_connsp_2(sK3,sK1,sK2) | v3_pre_topc(sK4,sK1) ),
% 1.57/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_494,plain,
% 1.57/0.99      ( m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.99      | k1_tops_1(sK1,X0) = X0
% 1.57/0.99      | sK4 != X0
% 1.57/0.99      | sK1 != sK1 ),
% 1.57/0.99      inference(resolution_lifted,[status(thm)],[c_372,c_14]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_495,plain,
% 1.57/0.99      ( m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.99      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.57/0.99      inference(unflattening,[status(thm)],[c_494]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_499,plain,
% 1.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.99      | m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.99      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.57/0.99      inference(global_propositional_subsumption,
% 1.57/0.99                [status(thm)],
% 1.57/0.99                [c_495,c_15]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_500,plain,
% 1.57/0.99      ( m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.99      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.57/0.99      inference(renaming,[status(thm)],[c_499]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_1364,plain,
% 1.57/0.99      ( m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/0.99      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.57/0.99      inference(subtyping,[status(esa)],[c_500]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_1382,plain,
% 1.57/0.99      ( m1_connsp_2(sK3,sK1,sK2)
% 1.57/0.99      | sP0_iProver_split
% 1.57/0.99      | k1_tops_1(sK1,sK4) = sK4 ),
% 1.57/0.99      inference(splitting,
% 1.57/0.99                [splitting(split),new_symbols(definition,[])],
% 1.57/0.99                [c_1364]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_1386,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.57/0.99  
% 1.57/0.99  cnf(c_1399,plain,
% 1.57/0.99      ( sK2 = sK2 ),
% 1.57/0.99      inference(instantiation,[status(thm)],[c_1386]) ).
% 1.57/0.99  
% 1.57/0.99  cnf(contradiction,plain,
% 1.57/0.99      ( $false ),
% 1.57/0.99      inference(minisat,
% 1.57/0.99                [status(thm)],
% 1.57/0.99                [c_2950,c_2586,c_2253,c_2197,c_2038,c_2004,c_1998,c_1971,
% 1.57/0.99                 c_1961,c_1954,c_1948,c_1382,c_1399,c_16,c_17]) ).
% 1.57/0.99  
% 1.57/0.99  
% 1.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.57/0.99  
% 1.57/0.99  ------                               Statistics
% 1.57/0.99  
% 1.57/0.99  ------ General
% 1.57/0.99  
% 1.57/0.99  abstr_ref_over_cycles:                  0
% 1.57/0.99  abstr_ref_under_cycles:                 0
% 1.57/0.99  gc_basic_clause_elim:                   0
% 1.57/0.99  forced_gc_time:                         0
% 1.57/0.99  parsing_time:                           0.008
% 1.57/0.99  unif_index_cands_time:                  0.
% 1.57/0.99  unif_index_add_time:                    0.
% 1.57/0.99  orderings_time:                         0.
% 1.57/0.99  out_proof_time:                         0.014
% 1.57/0.99  total_time:                             0.123
% 1.57/0.99  num_of_symbols:                         53
% 1.57/0.99  num_of_terms:                           1830
% 1.57/0.99  
% 1.57/0.99  ------ Preprocessing
% 1.57/0.99  
% 1.57/0.99  num_of_splits:                          5
% 1.57/0.99  num_of_split_atoms:                     3
% 1.57/0.99  num_of_reused_defs:                     2
% 1.57/0.99  num_eq_ax_congr_red:                    13
% 1.57/0.99  num_of_sem_filtered_clauses:            2
% 1.57/0.99  num_of_subtypes:                        3
% 1.57/0.99  monotx_restored_types:                  0
% 1.57/0.99  sat_num_of_epr_types:                   0
% 1.57/0.99  sat_num_of_non_cyclic_types:            0
% 1.57/0.99  sat_guarded_non_collapsed_types:        0
% 1.57/0.99  num_pure_diseq_elim:                    0
% 1.57/0.99  simp_replaced_by:                       0
% 1.57/0.99  res_preprocessed:                       92
% 1.57/0.99  prep_upred:                             0
% 1.57/0.99  prep_unflattend:                        38
% 1.57/0.99  smt_new_axioms:                         0
% 1.57/0.99  pred_elim_cands:                        4
% 1.57/0.99  pred_elim:                              4
% 1.57/0.99  pred_elim_cl:                           4
% 1.57/0.99  pred_elim_cycles:                       6
% 1.57/0.99  merged_defs:                            0
% 1.57/0.99  merged_defs_ncl:                        0
% 1.57/0.99  bin_hyper_res:                          0
% 1.57/0.99  prep_cycles:                            4
% 1.57/0.99  pred_elim_time:                         0.028
% 1.57/0.99  splitting_time:                         0.
% 1.57/0.99  sem_filter_time:                        0.
% 1.57/0.99  monotx_time:                            0.
% 1.57/0.99  subtype_inf_time:                       0.
% 1.57/0.99  
% 1.57/0.99  ------ Problem properties
% 1.57/0.99  
% 1.57/0.99  clauses:                                22
% 1.57/0.99  conjectures:                            5
% 1.57/0.99  epr:                                    5
% 1.57/0.99  horn:                                   15
% 1.57/0.99  ground:                                 8
% 1.57/0.99  unary:                                  2
% 1.57/0.99  binary:                                 11
% 1.57/0.99  lits:                                   57
% 1.57/0.99  lits_eq:                                3
% 1.57/0.99  fd_pure:                                0
% 1.57/0.99  fd_pseudo:                              0
% 1.57/0.99  fd_cond:                                0
% 1.57/0.99  fd_pseudo_cond:                         0
% 1.57/0.99  ac_symbols:                             0
% 1.57/0.99  
% 1.57/0.99  ------ Propositional Solver
% 1.57/0.99  
% 1.57/0.99  prop_solver_calls:                      26
% 1.57/0.99  prop_fast_solver_calls:                 857
% 1.57/0.99  smt_solver_calls:                       0
% 1.57/0.99  smt_fast_solver_calls:                  0
% 1.57/0.99  prop_num_of_clauses:                    814
% 1.57/0.99  prop_preprocess_simplified:             3255
% 1.57/0.99  prop_fo_subsumed:                       38
% 1.57/0.99  prop_solver_time:                       0.
% 1.57/0.99  smt_solver_time:                        0.
% 1.57/0.99  smt_fast_solver_time:                   0.
% 1.57/0.99  prop_fast_solver_time:                  0.
% 1.57/0.99  prop_unsat_core_time:                   0.
% 1.57/0.99  
% 1.57/0.99  ------ QBF
% 1.57/0.99  
% 1.57/0.99  qbf_q_res:                              0
% 1.57/0.99  qbf_num_tautologies:                    0
% 1.57/0.99  qbf_prep_cycles:                        0
% 1.57/0.99  
% 1.57/0.99  ------ BMC1
% 1.57/0.99  
% 1.57/0.99  bmc1_current_bound:                     -1
% 1.57/0.99  bmc1_last_solved_bound:                 -1
% 1.57/0.99  bmc1_unsat_core_size:                   -1
% 1.57/0.99  bmc1_unsat_core_parents_size:           -1
% 1.57/0.99  bmc1_merge_next_fun:                    0
% 1.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.57/0.99  
% 1.57/0.99  ------ Instantiation
% 1.57/0.99  
% 1.57/0.99  inst_num_of_clauses:                    196
% 1.57/0.99  inst_num_in_passive:                    15
% 1.57/0.99  inst_num_in_active:                     108
% 1.57/0.99  inst_num_in_unprocessed:                72
% 1.57/0.99  inst_num_of_loops:                      125
% 1.57/0.99  inst_num_of_learning_restarts:          0
% 1.57/0.99  inst_num_moves_active_passive:          14
% 1.57/0.99  inst_lit_activity:                      0
% 1.57/0.99  inst_lit_activity_moves:                0
% 1.57/0.99  inst_num_tautologies:                   0
% 1.57/0.99  inst_num_prop_implied:                  0
% 1.57/0.99  inst_num_existing_simplified:           0
% 1.57/0.99  inst_num_eq_res_simplified:             0
% 1.57/0.99  inst_num_child_elim:                    0
% 1.57/0.99  inst_num_of_dismatching_blockings:      20
% 1.57/0.99  inst_num_of_non_proper_insts:           130
% 1.57/0.99  inst_num_of_duplicates:                 0
% 1.57/0.99  inst_inst_num_from_inst_to_res:         0
% 1.57/0.99  inst_dismatching_checking_time:         0.
% 1.57/0.99  
% 1.57/0.99  ------ Resolution
% 1.57/0.99  
% 1.57/0.99  res_num_of_clauses:                     0
% 1.57/0.99  res_num_in_passive:                     0
% 1.57/0.99  res_num_in_active:                      0
% 1.57/0.99  res_num_of_loops:                       96
% 1.57/0.99  res_forward_subset_subsumed:            4
% 1.57/0.99  res_backward_subset_subsumed:           0
% 1.57/0.99  res_forward_subsumed:                   0
% 1.57/0.99  res_backward_subsumed:                  0
% 1.57/0.99  res_forward_subsumption_resolution:     1
% 1.57/0.99  res_backward_subsumption_resolution:    0
% 1.57/0.99  res_clause_to_clause_subsumption:       166
% 1.57/0.99  res_orphan_elimination:                 0
% 1.57/0.99  res_tautology_del:                      9
% 1.57/0.99  res_num_eq_res_simplified:              0
% 1.57/0.99  res_num_sel_changes:                    0
% 1.57/0.99  res_moves_from_active_to_pass:          0
% 1.57/0.99  
% 1.57/0.99  ------ Superposition
% 1.57/0.99  
% 1.57/0.99  sup_time_total:                         0.
% 1.57/0.99  sup_time_generating:                    0.
% 1.57/0.99  sup_time_sim_full:                      0.
% 1.57/0.99  sup_time_sim_immed:                     0.
% 1.57/0.99  
% 1.57/0.99  sup_num_of_clauses:                     41
% 1.57/0.99  sup_num_in_active:                      24
% 1.57/0.99  sup_num_in_passive:                     17
% 1.57/0.99  sup_num_of_loops:                       24
% 1.57/0.99  sup_fw_superposition:                   15
% 1.57/0.99  sup_bw_superposition:                   10
% 1.57/0.99  sup_immediate_simplified:               0
% 1.57/0.99  sup_given_eliminated:                   0
% 1.57/0.99  comparisons_done:                       0
% 1.57/0.99  comparisons_avoided:                    0
% 1.57/0.99  
% 1.57/0.99  ------ Simplifications
% 1.57/0.99  
% 1.57/0.99  
% 1.57/0.99  sim_fw_subset_subsumed:                 0
% 1.57/0.99  sim_bw_subset_subsumed:                 0
% 1.57/0.99  sim_fw_subsumed:                        0
% 1.57/0.99  sim_bw_subsumed:                        0
% 1.57/0.99  sim_fw_subsumption_res:                 0
% 1.57/0.99  sim_bw_subsumption_res:                 0
% 1.57/0.99  sim_tautology_del:                      2
% 1.57/0.99  sim_eq_tautology_del:                   0
% 1.57/0.99  sim_eq_res_simp:                        0
% 1.57/0.99  sim_fw_demodulated:                     0
% 1.57/0.99  sim_bw_demodulated:                     0
% 1.57/0.99  sim_light_normalised:                   0
% 1.57/0.99  sim_joinable_taut:                      0
% 1.57/0.99  sim_joinable_simp:                      0
% 1.57/0.99  sim_ac_normalised:                      0
% 1.57/0.99  sim_smt_subsumption:                    0
% 1.57/0.99  
%------------------------------------------------------------------------------
