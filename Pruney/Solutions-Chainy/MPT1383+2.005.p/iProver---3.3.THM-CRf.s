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
% DateTime   : Thu Dec  3 12:18:21 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 491 expanded)
%              Number of clauses        :   65 (  85 expanded)
%              Number of leaves         :   13 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          :  703 (5632 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK5)
        & r1_tarski(sK5,X2)
        & v3_pre_topc(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
              | ~ r1_tarski(X3,sK4)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_connsp_2(sK4,X0,X1) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,sK4)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | m1_connsp_2(sK4,X0,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                  ( ~ r2_hidden(sK3,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,sK3) )
            & ( ? [X4] :
                  ( r2_hidden(sK3,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | m1_connsp_2(X2,X0,sK3) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
                    | ~ v3_pre_topc(X3,sK2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                | ~ m1_connsp_2(X2,sK2,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK2)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
                | m1_connsp_2(X2,sK2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK3,X3)
          | ~ r1_tarski(X3,sK4)
          | ~ v3_pre_topc(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ m1_connsp_2(sK4,sK2,sK3) )
    & ( ( r2_hidden(sK3,sK5)
        & r1_tarski(sK5,sK4)
        & v3_pre_topc(sK5,sK2)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) )
      | m1_connsp_2(sK4,sK2,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f41,f40,f39,f38])).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3,X3)
      | ~ r1_tarski(X3,sK4)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_connsp_2(sK4,sK2,sK3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_connsp_2(sK1(X0,X1,X2),X0,X1)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK1(X0,X1,X2),X2)
                & v3_pre_topc(sK1(X0,X1,X2),X0)
                & m1_connsp_2(sK1(X0,X1,X2),X0,X1)
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,
    ( r2_hidden(sK3,sK5)
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,
    ( r1_tarski(sK5,sK4)
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,
    ( v3_pre_topc(sK5,sK2)
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1039,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | r2_hidden(X0_45,X2_45)
    | ~ r1_tarski(X1_45,X2_45) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1236,plain,
    ( r2_hidden(sK3,X0_45)
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(sK5,X0_45) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_1438,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,X0_45))
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(sK5,k1_tops_1(sK2,X0_45)) ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_1591,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(sK5,k1_tops_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_649,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK2,X1)) ),
    inference(resolution,[status(thm)],[c_6,c_22])).

cnf(c_1020,plain,
    ( ~ v3_pre_topc(X0_45,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0_45,X1_45)
    | r1_tarski(X0_45,k1_tops_1(sK2,X1_45)) ),
    inference(subtyping,[status(esa)],[c_649])).

cnf(c_1228,plain,
    ( ~ v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK5,X0_45)
    | r1_tarski(sK5,k1_tops_1(sK2,X0_45)) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_1456,plain,
    ( ~ v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK5,k1_tops_1(sK2,sK4))
    | ~ r1_tarski(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1228])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_9])).

cnf(c_168,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_473,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_168,c_23])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_477,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_24,c_22])).

cnf(c_1027,plain,
    ( ~ m1_connsp_2(X0_45,sK2,X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | r2_hidden(X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1284,plain,
    ( ~ m1_connsp_2(sK1(sK2,sK3,sK4),sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,sK1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_15,negated_conjecture,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,X0)
    | ~ r1_tarski(X0,sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1035,negated_conjecture,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ v3_pre_topc(X0_45,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,X0_45)
    | ~ r1_tarski(X0_45,sK4) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1193,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ v3_pre_topc(sK1(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,sK1(sK2,sK3,sK4))
    | ~ r1_tarski(sK1(sK2,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_9])).

cnf(c_161,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_160])).

cnf(c_493,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,X1,X0),X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_161,c_23])).

cnf(c_497,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,X1,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_24,c_22])).

cnf(c_1026,plain,
    ( ~ m1_connsp_2(X0_45,sK2,X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,X1_45,X0_45),X0_45) ),
    inference(subtyping,[status(esa)],[c_497])).

cnf(c_1179,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_146,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_9])).

cnf(c_147,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_533,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | m1_connsp_2(sK1(sK2,X1,X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_147,c_23])).

cnf(c_537,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | m1_connsp_2(sK1(sK2,X1,X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_24,c_22])).

cnf(c_1024,plain,
    ( ~ m1_connsp_2(X0_45,sK2,X1_45)
    | m1_connsp_2(sK1(sK2,X1_45,X0_45),sK2,X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_537])).

cnf(c_1176,plain,
    ( m1_connsp_2(sK1(sK2,sK3,sK4),sK2,sK3)
    | ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_593,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_7,c_23])).

cnf(c_597,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_24,c_22])).

cnf(c_1021,plain,
    ( m1_connsp_2(X0_45,sK2,X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_45,k1_tops_1(sK2,X0_45)) ),
    inference(subtyping,[status(esa)],[c_597])).

cnf(c_1171,plain,
    ( m1_connsp_2(sK4,sK2,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_45,k1_tops_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_1173,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_153,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_9])).

cnf(c_154,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_513,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | v3_pre_topc(sK1(sK2,X1,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_154,c_23])).

cnf(c_517,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | v3_pre_topc(sK1(sK2,X1,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_24,c_22])).

cnf(c_1025,plain,
    ( ~ m1_connsp_2(X0_45,sK2,X1_45)
    | v3_pre_topc(sK1(sK2,X1_45,X0_45),sK2)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_517])).

cnf(c_1162,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | v3_pre_topc(sK1(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_139,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_9])).

cnf(c_140,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_553,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_140,c_23])).

cnf(c_557,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_24,c_22])).

cnf(c_1023,plain,
    ( ~ m1_connsp_2(X0_45,sK2,X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1_45,X0_45),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_557])).

cnf(c_1159,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(sK4,sK2,sK3)
    | r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(sK4,sK2,sK3)
    | r1_tarski(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,negated_conjecture,
    ( m1_connsp_2(sK4,sK2,sK3)
    | v3_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_19,negated_conjecture,
    ( m1_connsp_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1591,c_1456,c_1284,c_1193,c_1179,c_1176,c_1173,c_1162,c_1159,c_16,c_17,c_18,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.17/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.17/0.99  
% 1.17/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.17/0.99  
% 1.17/0.99  ------  iProver source info
% 1.17/0.99  
% 1.17/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.17/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.17/0.99  git: non_committed_changes: false
% 1.17/0.99  git: last_make_outside_of_git: false
% 1.17/0.99  
% 1.17/0.99  ------ 
% 1.17/0.99  
% 1.17/0.99  ------ Input Options
% 1.17/0.99  
% 1.17/0.99  --out_options                           all
% 1.17/0.99  --tptp_safe_out                         true
% 1.17/0.99  --problem_path                          ""
% 1.17/0.99  --include_path                          ""
% 1.17/0.99  --clausifier                            res/vclausify_rel
% 1.17/0.99  --clausifier_options                    --mode clausify
% 1.17/0.99  --stdin                                 false
% 1.17/0.99  --stats_out                             all
% 1.17/0.99  
% 1.17/0.99  ------ General Options
% 1.17/0.99  
% 1.17/0.99  --fof                                   false
% 1.17/0.99  --time_out_real                         305.
% 1.17/0.99  --time_out_virtual                      -1.
% 1.17/0.99  --symbol_type_check                     false
% 1.17/0.99  --clausify_out                          false
% 1.17/0.99  --sig_cnt_out                           false
% 1.17/0.99  --trig_cnt_out                          false
% 1.17/0.99  --trig_cnt_out_tolerance                1.
% 1.17/0.99  --trig_cnt_out_sk_spl                   false
% 1.17/0.99  --abstr_cl_out                          false
% 1.17/0.99  
% 1.17/0.99  ------ Global Options
% 1.17/0.99  
% 1.17/0.99  --schedule                              default
% 1.17/0.99  --add_important_lit                     false
% 1.17/0.99  --prop_solver_per_cl                    1000
% 1.17/0.99  --min_unsat_core                        false
% 1.17/0.99  --soft_assumptions                      false
% 1.17/0.99  --soft_lemma_size                       3
% 1.17/0.99  --prop_impl_unit_size                   0
% 1.17/0.99  --prop_impl_unit                        []
% 1.17/0.99  --share_sel_clauses                     true
% 1.17/0.99  --reset_solvers                         false
% 1.17/0.99  --bc_imp_inh                            [conj_cone]
% 1.17/0.99  --conj_cone_tolerance                   3.
% 1.17/0.99  --extra_neg_conj                        none
% 1.17/0.99  --large_theory_mode                     true
% 1.17/0.99  --prolific_symb_bound                   200
% 1.17/0.99  --lt_threshold                          2000
% 1.17/0.99  --clause_weak_htbl                      true
% 1.17/0.99  --gc_record_bc_elim                     false
% 1.17/0.99  
% 1.17/0.99  ------ Preprocessing Options
% 1.17/0.99  
% 1.17/0.99  --preprocessing_flag                    true
% 1.17/0.99  --time_out_prep_mult                    0.1
% 1.17/0.99  --splitting_mode                        input
% 1.17/0.99  --splitting_grd                         true
% 1.17/0.99  --splitting_cvd                         false
% 1.17/0.99  --splitting_cvd_svl                     false
% 1.17/0.99  --splitting_nvd                         32
% 1.17/0.99  --sub_typing                            true
% 1.17/0.99  --prep_gs_sim                           true
% 1.17/0.99  --prep_unflatten                        true
% 1.17/0.99  --prep_res_sim                          true
% 1.17/0.99  --prep_upred                            true
% 1.17/0.99  --prep_sem_filter                       exhaustive
% 1.17/0.99  --prep_sem_filter_out                   false
% 1.17/0.99  --pred_elim                             true
% 1.17/0.99  --res_sim_input                         true
% 1.17/0.99  --eq_ax_congr_red                       true
% 1.17/0.99  --pure_diseq_elim                       true
% 1.17/0.99  --brand_transform                       false
% 1.17/0.99  --non_eq_to_eq                          false
% 1.17/0.99  --prep_def_merge                        true
% 1.17/0.99  --prep_def_merge_prop_impl              false
% 1.17/0.99  --prep_def_merge_mbd                    true
% 1.17/0.99  --prep_def_merge_tr_red                 false
% 1.17/0.99  --prep_def_merge_tr_cl                  false
% 1.17/0.99  --smt_preprocessing                     true
% 1.17/0.99  --smt_ac_axioms                         fast
% 1.17/0.99  --preprocessed_out                      false
% 1.17/0.99  --preprocessed_stats                    false
% 1.17/0.99  
% 1.17/0.99  ------ Abstraction refinement Options
% 1.17/0.99  
% 1.17/0.99  --abstr_ref                             []
% 1.17/0.99  --abstr_ref_prep                        false
% 1.17/0.99  --abstr_ref_until_sat                   false
% 1.17/0.99  --abstr_ref_sig_restrict                funpre
% 1.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/0.99  --abstr_ref_under                       []
% 1.17/0.99  
% 1.17/0.99  ------ SAT Options
% 1.17/0.99  
% 1.17/0.99  --sat_mode                              false
% 1.17/0.99  --sat_fm_restart_options                ""
% 1.17/0.99  --sat_gr_def                            false
% 1.17/0.99  --sat_epr_types                         true
% 1.17/0.99  --sat_non_cyclic_types                  false
% 1.17/0.99  --sat_finite_models                     false
% 1.17/0.99  --sat_fm_lemmas                         false
% 1.17/0.99  --sat_fm_prep                           false
% 1.17/0.99  --sat_fm_uc_incr                        true
% 1.17/0.99  --sat_out_model                         small
% 1.17/0.99  --sat_out_clauses                       false
% 1.17/0.99  
% 1.17/0.99  ------ QBF Options
% 1.17/0.99  
% 1.17/0.99  --qbf_mode                              false
% 1.17/0.99  --qbf_elim_univ                         false
% 1.17/0.99  --qbf_dom_inst                          none
% 1.17/0.99  --qbf_dom_pre_inst                      false
% 1.17/0.99  --qbf_sk_in                             false
% 1.17/0.99  --qbf_pred_elim                         true
% 1.17/0.99  --qbf_split                             512
% 1.17/0.99  
% 1.17/0.99  ------ BMC1 Options
% 1.17/0.99  
% 1.17/0.99  --bmc1_incremental                      false
% 1.17/0.99  --bmc1_axioms                           reachable_all
% 1.17/0.99  --bmc1_min_bound                        0
% 1.17/0.99  --bmc1_max_bound                        -1
% 1.17/0.99  --bmc1_max_bound_default                -1
% 1.17/0.99  --bmc1_symbol_reachability              true
% 1.17/0.99  --bmc1_property_lemmas                  false
% 1.17/0.99  --bmc1_k_induction                      false
% 1.17/0.99  --bmc1_non_equiv_states                 false
% 1.17/0.99  --bmc1_deadlock                         false
% 1.17/0.99  --bmc1_ucm                              false
% 1.17/0.99  --bmc1_add_unsat_core                   none
% 1.17/0.99  --bmc1_unsat_core_children              false
% 1.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/0.99  --bmc1_out_stat                         full
% 1.17/0.99  --bmc1_ground_init                      false
% 1.17/0.99  --bmc1_pre_inst_next_state              false
% 1.17/0.99  --bmc1_pre_inst_state                   false
% 1.17/0.99  --bmc1_pre_inst_reach_state             false
% 1.17/0.99  --bmc1_out_unsat_core                   false
% 1.17/0.99  --bmc1_aig_witness_out                  false
% 1.17/0.99  --bmc1_verbose                          false
% 1.17/0.99  --bmc1_dump_clauses_tptp                false
% 1.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.17/0.99  --bmc1_dump_file                        -
% 1.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.17/0.99  --bmc1_ucm_extend_mode                  1
% 1.17/0.99  --bmc1_ucm_init_mode                    2
% 1.17/0.99  --bmc1_ucm_cone_mode                    none
% 1.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.17/0.99  --bmc1_ucm_relax_model                  4
% 1.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/0.99  --bmc1_ucm_layered_model                none
% 1.17/0.99  --bmc1_ucm_max_lemma_size               10
% 1.17/0.99  
% 1.17/0.99  ------ AIG Options
% 1.17/0.99  
% 1.17/0.99  --aig_mode                              false
% 1.17/0.99  
% 1.17/0.99  ------ Instantiation Options
% 1.17/0.99  
% 1.17/0.99  --instantiation_flag                    true
% 1.17/0.99  --inst_sos_flag                         false
% 1.17/0.99  --inst_sos_phase                        true
% 1.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/0.99  --inst_lit_sel_side                     num_symb
% 1.17/0.99  --inst_solver_per_active                1400
% 1.17/0.99  --inst_solver_calls_frac                1.
% 1.17/0.99  --inst_passive_queue_type               priority_queues
% 1.17/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/0.99  --inst_passive_queues_freq              [25;2]
% 1.17/0.99  --inst_dismatching                      true
% 1.17/0.99  --inst_eager_unprocessed_to_passive     true
% 1.17/0.99  --inst_prop_sim_given                   true
% 1.17/0.99  --inst_prop_sim_new                     false
% 1.17/0.99  --inst_subs_new                         false
% 1.17/0.99  --inst_eq_res_simp                      false
% 1.17/0.99  --inst_subs_given                       false
% 1.17/0.99  --inst_orphan_elimination               true
% 1.17/0.99  --inst_learning_loop_flag               true
% 1.17/0.99  --inst_learning_start                   3000
% 1.17/0.99  --inst_learning_factor                  2
% 1.17/0.99  --inst_start_prop_sim_after_learn       3
% 1.17/0.99  --inst_sel_renew                        solver
% 1.17/0.99  --inst_lit_activity_flag                true
% 1.17/0.99  --inst_restr_to_given                   false
% 1.17/0.99  --inst_activity_threshold               500
% 1.17/0.99  --inst_out_proof                        true
% 1.17/0.99  
% 1.17/0.99  ------ Resolution Options
% 1.17/0.99  
% 1.17/0.99  --resolution_flag                       true
% 1.17/0.99  --res_lit_sel                           adaptive
% 1.17/0.99  --res_lit_sel_side                      none
% 1.17/0.99  --res_ordering                          kbo
% 1.17/0.99  --res_to_prop_solver                    active
% 1.17/0.99  --res_prop_simpl_new                    false
% 1.17/0.99  --res_prop_simpl_given                  true
% 1.17/0.99  --res_passive_queue_type                priority_queues
% 1.17/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/0.99  --res_passive_queues_freq               [15;5]
% 1.17/0.99  --res_forward_subs                      full
% 1.17/0.99  --res_backward_subs                     full
% 1.17/0.99  --res_forward_subs_resolution           true
% 1.17/0.99  --res_backward_subs_resolution          true
% 1.17/0.99  --res_orphan_elimination                true
% 1.17/0.99  --res_time_limit                        2.
% 1.17/0.99  --res_out_proof                         true
% 1.17/0.99  
% 1.17/0.99  ------ Superposition Options
% 1.17/0.99  
% 1.17/0.99  --superposition_flag                    true
% 1.17/0.99  --sup_passive_queue_type                priority_queues
% 1.17/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.17/0.99  --demod_completeness_check              fast
% 1.17/0.99  --demod_use_ground                      true
% 1.17/0.99  --sup_to_prop_solver                    passive
% 1.17/0.99  --sup_prop_simpl_new                    true
% 1.17/0.99  --sup_prop_simpl_given                  true
% 1.17/0.99  --sup_fun_splitting                     false
% 1.17/0.99  --sup_smt_interval                      50000
% 1.17/0.99  
% 1.17/0.99  ------ Superposition Simplification Setup
% 1.17/0.99  
% 1.17/0.99  --sup_indices_passive                   []
% 1.17/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.99  --sup_full_bw                           [BwDemod]
% 1.17/0.99  --sup_immed_triv                        [TrivRules]
% 1.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.99  --sup_immed_bw_main                     []
% 1.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.99  
% 1.17/0.99  ------ Combination Options
% 1.17/0.99  
% 1.17/0.99  --comb_res_mult                         3
% 1.17/0.99  --comb_sup_mult                         2
% 1.17/0.99  --comb_inst_mult                        10
% 1.17/0.99  
% 1.17/0.99  ------ Debug Options
% 1.17/0.99  
% 1.17/0.99  --dbg_backtrace                         false
% 1.17/0.99  --dbg_dump_prop_clauses                 false
% 1.17/0.99  --dbg_dump_prop_clauses_file            -
% 1.17/0.99  --dbg_out_stat                          false
% 1.17/0.99  ------ Parsing...
% 1.17/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.17/0.99  
% 1.17/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.17/0.99  
% 1.17/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.17/0.99  ------ Proving...
% 1.17/0.99  ------ Problem Properties 
% 1.17/0.99  
% 1.17/0.99  
% 1.17/0.99  clauses                                 22
% 1.17/0.99  conjectures                             7
% 1.17/0.99  EPR                                     5
% 1.17/0.99  Horn                                    17
% 1.17/0.99  unary                                   2
% 1.17/0.99  binary                                  8
% 1.17/0.99  lits                                    59
% 1.17/0.99  lits eq                                 0
% 1.17/0.99  fd_pure                                 0
% 1.17/0.99  fd_pseudo                               0
% 1.17/0.99  fd_cond                                 0
% 1.17/0.99  fd_pseudo_cond                          0
% 1.17/0.99  AC symbols                              0
% 1.17/0.99  
% 1.17/0.99  ------ Schedule dynamic 5 is on 
% 1.17/0.99  
% 1.17/0.99  ------ no equalities: superposition off 
% 1.17/0.99  
% 1.17/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.17/0.99  
% 1.17/0.99  
% 1.17/0.99  ------ 
% 1.17/0.99  Current options:
% 1.17/0.99  ------ 
% 1.17/0.99  
% 1.17/0.99  ------ Input Options
% 1.17/0.99  
% 1.17/0.99  --out_options                           all
% 1.17/0.99  --tptp_safe_out                         true
% 1.17/0.99  --problem_path                          ""
% 1.17/0.99  --include_path                          ""
% 1.17/0.99  --clausifier                            res/vclausify_rel
% 1.17/0.99  --clausifier_options                    --mode clausify
% 1.17/0.99  --stdin                                 false
% 1.17/0.99  --stats_out                             all
% 1.17/0.99  
% 1.17/0.99  ------ General Options
% 1.17/0.99  
% 1.17/0.99  --fof                                   false
% 1.17/0.99  --time_out_real                         305.
% 1.17/0.99  --time_out_virtual                      -1.
% 1.17/0.99  --symbol_type_check                     false
% 1.17/0.99  --clausify_out                          false
% 1.17/0.99  --sig_cnt_out                           false
% 1.17/0.99  --trig_cnt_out                          false
% 1.17/0.99  --trig_cnt_out_tolerance                1.
% 1.17/0.99  --trig_cnt_out_sk_spl                   false
% 1.17/0.99  --abstr_cl_out                          false
% 1.17/0.99  
% 1.17/0.99  ------ Global Options
% 1.17/0.99  
% 1.17/0.99  --schedule                              default
% 1.17/0.99  --add_important_lit                     false
% 1.17/0.99  --prop_solver_per_cl                    1000
% 1.17/0.99  --min_unsat_core                        false
% 1.17/0.99  --soft_assumptions                      false
% 1.17/0.99  --soft_lemma_size                       3
% 1.17/0.99  --prop_impl_unit_size                   0
% 1.17/0.99  --prop_impl_unit                        []
% 1.17/0.99  --share_sel_clauses                     true
% 1.17/0.99  --reset_solvers                         false
% 1.17/0.99  --bc_imp_inh                            [conj_cone]
% 1.17/0.99  --conj_cone_tolerance                   3.
% 1.17/0.99  --extra_neg_conj                        none
% 1.17/0.99  --large_theory_mode                     true
% 1.17/0.99  --prolific_symb_bound                   200
% 1.17/0.99  --lt_threshold                          2000
% 1.17/0.99  --clause_weak_htbl                      true
% 1.17/0.99  --gc_record_bc_elim                     false
% 1.17/0.99  
% 1.17/0.99  ------ Preprocessing Options
% 1.17/0.99  
% 1.17/0.99  --preprocessing_flag                    true
% 1.17/0.99  --time_out_prep_mult                    0.1
% 1.17/0.99  --splitting_mode                        input
% 1.17/0.99  --splitting_grd                         true
% 1.17/0.99  --splitting_cvd                         false
% 1.17/0.99  --splitting_cvd_svl                     false
% 1.17/0.99  --splitting_nvd                         32
% 1.17/0.99  --sub_typing                            true
% 1.17/0.99  --prep_gs_sim                           true
% 1.17/0.99  --prep_unflatten                        true
% 1.17/0.99  --prep_res_sim                          true
% 1.17/0.99  --prep_upred                            true
% 1.17/0.99  --prep_sem_filter                       exhaustive
% 1.17/0.99  --prep_sem_filter_out                   false
% 1.17/0.99  --pred_elim                             true
% 1.17/0.99  --res_sim_input                         true
% 1.17/0.99  --eq_ax_congr_red                       true
% 1.17/0.99  --pure_diseq_elim                       true
% 1.17/0.99  --brand_transform                       false
% 1.17/0.99  --non_eq_to_eq                          false
% 1.17/0.99  --prep_def_merge                        true
% 1.17/0.99  --prep_def_merge_prop_impl              false
% 1.17/0.99  --prep_def_merge_mbd                    true
% 1.17/0.99  --prep_def_merge_tr_red                 false
% 1.17/0.99  --prep_def_merge_tr_cl                  false
% 1.17/0.99  --smt_preprocessing                     true
% 1.17/0.99  --smt_ac_axioms                         fast
% 1.17/0.99  --preprocessed_out                      false
% 1.17/0.99  --preprocessed_stats                    false
% 1.17/0.99  
% 1.17/0.99  ------ Abstraction refinement Options
% 1.17/0.99  
% 1.17/0.99  --abstr_ref                             []
% 1.17/0.99  --abstr_ref_prep                        false
% 1.17/0.99  --abstr_ref_until_sat                   false
% 1.17/0.99  --abstr_ref_sig_restrict                funpre
% 1.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/0.99  --abstr_ref_under                       []
% 1.17/0.99  
% 1.17/0.99  ------ SAT Options
% 1.17/0.99  
% 1.17/0.99  --sat_mode                              false
% 1.17/0.99  --sat_fm_restart_options                ""
% 1.17/0.99  --sat_gr_def                            false
% 1.17/0.99  --sat_epr_types                         true
% 1.17/0.99  --sat_non_cyclic_types                  false
% 1.17/0.99  --sat_finite_models                     false
% 1.17/0.99  --sat_fm_lemmas                         false
% 1.17/0.99  --sat_fm_prep                           false
% 1.17/0.99  --sat_fm_uc_incr                        true
% 1.17/0.99  --sat_out_model                         small
% 1.17/0.99  --sat_out_clauses                       false
% 1.17/0.99  
% 1.17/0.99  ------ QBF Options
% 1.17/0.99  
% 1.17/0.99  --qbf_mode                              false
% 1.17/0.99  --qbf_elim_univ                         false
% 1.17/0.99  --qbf_dom_inst                          none
% 1.17/0.99  --qbf_dom_pre_inst                      false
% 1.17/0.99  --qbf_sk_in                             false
% 1.17/0.99  --qbf_pred_elim                         true
% 1.17/0.99  --qbf_split                             512
% 1.17/0.99  
% 1.17/0.99  ------ BMC1 Options
% 1.17/0.99  
% 1.17/0.99  --bmc1_incremental                      false
% 1.17/0.99  --bmc1_axioms                           reachable_all
% 1.17/0.99  --bmc1_min_bound                        0
% 1.17/0.99  --bmc1_max_bound                        -1
% 1.17/0.99  --bmc1_max_bound_default                -1
% 1.17/0.99  --bmc1_symbol_reachability              true
% 1.17/0.99  --bmc1_property_lemmas                  false
% 1.17/0.99  --bmc1_k_induction                      false
% 1.17/0.99  --bmc1_non_equiv_states                 false
% 1.17/0.99  --bmc1_deadlock                         false
% 1.17/0.99  --bmc1_ucm                              false
% 1.17/0.99  --bmc1_add_unsat_core                   none
% 1.17/0.99  --bmc1_unsat_core_children              false
% 1.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/0.99  --bmc1_out_stat                         full
% 1.17/0.99  --bmc1_ground_init                      false
% 1.17/0.99  --bmc1_pre_inst_next_state              false
% 1.17/0.99  --bmc1_pre_inst_state                   false
% 1.17/0.99  --bmc1_pre_inst_reach_state             false
% 1.17/0.99  --bmc1_out_unsat_core                   false
% 1.17/0.99  --bmc1_aig_witness_out                  false
% 1.17/0.99  --bmc1_verbose                          false
% 1.17/0.99  --bmc1_dump_clauses_tptp                false
% 1.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.17/0.99  --bmc1_dump_file                        -
% 1.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.17/0.99  --bmc1_ucm_extend_mode                  1
% 1.17/0.99  --bmc1_ucm_init_mode                    2
% 1.17/0.99  --bmc1_ucm_cone_mode                    none
% 1.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.17/0.99  --bmc1_ucm_relax_model                  4
% 1.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/0.99  --bmc1_ucm_layered_model                none
% 1.17/0.99  --bmc1_ucm_max_lemma_size               10
% 1.17/0.99  
% 1.17/0.99  ------ AIG Options
% 1.17/0.99  
% 1.17/0.99  --aig_mode                              false
% 1.17/0.99  
% 1.17/0.99  ------ Instantiation Options
% 1.17/0.99  
% 1.17/0.99  --instantiation_flag                    true
% 1.17/0.99  --inst_sos_flag                         false
% 1.17/0.99  --inst_sos_phase                        true
% 1.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/0.99  --inst_lit_sel_side                     none
% 1.17/0.99  --inst_solver_per_active                1400
% 1.17/0.99  --inst_solver_calls_frac                1.
% 1.17/0.99  --inst_passive_queue_type               priority_queues
% 1.17/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/0.99  --inst_passive_queues_freq              [25;2]
% 1.17/0.99  --inst_dismatching                      true
% 1.17/0.99  --inst_eager_unprocessed_to_passive     true
% 1.17/0.99  --inst_prop_sim_given                   true
% 1.17/0.99  --inst_prop_sim_new                     false
% 1.17/0.99  --inst_subs_new                         false
% 1.17/0.99  --inst_eq_res_simp                      false
% 1.17/0.99  --inst_subs_given                       false
% 1.17/0.99  --inst_orphan_elimination               true
% 1.17/0.99  --inst_learning_loop_flag               true
% 1.17/0.99  --inst_learning_start                   3000
% 1.17/0.99  --inst_learning_factor                  2
% 1.17/0.99  --inst_start_prop_sim_after_learn       3
% 1.17/0.99  --inst_sel_renew                        solver
% 1.17/0.99  --inst_lit_activity_flag                true
% 1.17/0.99  --inst_restr_to_given                   false
% 1.17/0.99  --inst_activity_threshold               500
% 1.17/0.99  --inst_out_proof                        true
% 1.17/0.99  
% 1.17/0.99  ------ Resolution Options
% 1.17/0.99  
% 1.17/0.99  --resolution_flag                       false
% 1.17/0.99  --res_lit_sel                           adaptive
% 1.17/0.99  --res_lit_sel_side                      none
% 1.17/0.99  --res_ordering                          kbo
% 1.17/0.99  --res_to_prop_solver                    active
% 1.17/0.99  --res_prop_simpl_new                    false
% 1.17/0.99  --res_prop_simpl_given                  true
% 1.17/0.99  --res_passive_queue_type                priority_queues
% 1.17/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/0.99  --res_passive_queues_freq               [15;5]
% 1.17/0.99  --res_forward_subs                      full
% 1.17/0.99  --res_backward_subs                     full
% 1.17/0.99  --res_forward_subs_resolution           true
% 1.17/0.99  --res_backward_subs_resolution          true
% 1.17/0.99  --res_orphan_elimination                true
% 1.17/0.99  --res_time_limit                        2.
% 1.17/0.99  --res_out_proof                         true
% 1.17/0.99  
% 1.17/0.99  ------ Superposition Options
% 1.17/0.99  
% 1.17/0.99  --superposition_flag                    false
% 1.17/0.99  --sup_passive_queue_type                priority_queues
% 1.17/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.17/0.99  --demod_completeness_check              fast
% 1.17/0.99  --demod_use_ground                      true
% 1.17/0.99  --sup_to_prop_solver                    passive
% 1.17/0.99  --sup_prop_simpl_new                    true
% 1.17/0.99  --sup_prop_simpl_given                  true
% 1.17/0.99  --sup_fun_splitting                     false
% 1.17/0.99  --sup_smt_interval                      50000
% 1.17/0.99  
% 1.17/0.99  ------ Superposition Simplification Setup
% 1.17/0.99  
% 1.17/0.99  --sup_indices_passive                   []
% 1.17/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.99  --sup_full_bw                           [BwDemod]
% 1.17/0.99  --sup_immed_triv                        [TrivRules]
% 1.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.99  --sup_immed_bw_main                     []
% 1.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.99  
% 1.17/0.99  ------ Combination Options
% 1.17/0.99  
% 1.17/0.99  --comb_res_mult                         3
% 1.17/0.99  --comb_sup_mult                         2
% 1.17/0.99  --comb_inst_mult                        10
% 1.17/0.99  
% 1.17/0.99  ------ Debug Options
% 1.17/0.99  
% 1.17/0.99  --dbg_backtrace                         false
% 1.17/0.99  --dbg_dump_prop_clauses                 false
% 1.17/0.99  --dbg_dump_prop_clauses_file            -
% 1.17/0.99  --dbg_out_stat                          false
% 1.17/0.99  
% 1.17/0.99  
% 1.17/0.99  
% 1.17/0.99  
% 1.17/0.99  ------ Proving...
% 1.17/0.99  
% 1.17/0.99  
% 1.17/0.99  % SZS status Theorem for theBenchmark.p
% 1.17/0.99  
% 1.17/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.17/0.99  
% 1.17/0.99  fof(f1,axiom,(
% 1.17/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.99  
% 1.17/0.99  fof(f12,plain,(
% 1.17/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.17/0.99    inference(ennf_transformation,[],[f1])).
% 1.17/0.99  
% 1.17/0.99  fof(f27,plain,(
% 1.17/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.17/0.99    inference(nnf_transformation,[],[f12])).
% 1.17/0.99  
% 1.17/0.99  fof(f28,plain,(
% 1.17/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.17/0.99    inference(rectify,[],[f27])).
% 1.17/0.99  
% 1.17/0.99  fof(f29,plain,(
% 1.17/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.17/0.99    introduced(choice_axiom,[])).
% 1.17/0.99  
% 1.17/0.99  fof(f30,plain,(
% 1.17/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 1.17/0.99  
% 1.17/0.99  fof(f43,plain,(
% 1.17/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f30])).
% 1.17/0.99  
% 1.17/0.99  fof(f4,axiom,(
% 1.17/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.99  
% 1.17/0.99  fof(f15,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.99    inference(ennf_transformation,[],[f4])).
% 1.17/0.99  
% 1.17/0.99  fof(f16,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.99    inference(flattening,[],[f15])).
% 1.17/0.99  
% 1.17/0.99  fof(f49,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f16])).
% 1.17/0.99  
% 1.17/0.99  fof(f9,conjecture,(
% 1.17/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.99  
% 1.17/0.99  fof(f10,negated_conjecture,(
% 1.17/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.17/0.99    inference(negated_conjecture,[],[f9])).
% 1.17/0.99  
% 1.17/0.99  fof(f25,plain,(
% 1.17/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.17/0.99    inference(ennf_transformation,[],[f10])).
% 1.17/0.99  
% 1.17/0.99  fof(f26,plain,(
% 1.17/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/0.99    inference(flattening,[],[f25])).
% 1.17/0.99  
% 1.17/0.99  fof(f35,plain,(
% 1.17/0.99    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/0.99    inference(nnf_transformation,[],[f26])).
% 1.17/0.99  
% 1.17/0.99  fof(f36,plain,(
% 1.17/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/0.99    inference(flattening,[],[f35])).
% 1.17/0.99  
% 1.17/0.99  fof(f37,plain,(
% 1.17/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/0.99    inference(rectify,[],[f36])).
% 1.17/0.99  
% 1.17/0.99  fof(f41,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK5) & r1_tarski(sK5,X2) & v3_pre_topc(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.17/0.99    introduced(choice_axiom,[])).
% 1.17/0.99  
% 1.17/0.99  fof(f40,plain,(
% 1.17/0.99    ( ! [X0,X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(sK4,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,sK4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(sK4,X0,X1)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.17/0.99    introduced(choice_axiom,[])).
% 1.17/0.99  
% 1.17/0.99  fof(f39,plain,(
% 1.17/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK3,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,sK3)) & (? [X4] : (r2_hidden(sK3,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,sK3)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.17/0.99    introduced(choice_axiom,[])).
% 1.17/0.99  
% 1.17/0.99  fof(f38,plain,(
% 1.17/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~m1_connsp_2(X2,sK2,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) | m1_connsp_2(X2,sK2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.17/0.99    introduced(choice_axiom,[])).
% 1.17/0.99  
% 1.17/0.99  fof(f42,plain,(
% 1.17/0.99    (((! [X3] : (~r2_hidden(sK3,X3) | ~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~m1_connsp_2(sK4,sK2,sK3)) & ((r2_hidden(sK3,sK5) & r1_tarski(sK5,sK4) & v3_pre_topc(sK5,sK2) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) | m1_connsp_2(sK4,sK2,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f41,f40,f39,f38])).
% 1.17/0.99  
% 1.17/0.99  fof(f60,plain,(
% 1.17/0.99    l1_pre_topc(sK2)),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f7,axiom,(
% 1.17/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.99  
% 1.17/0.99  fof(f21,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/0.99    inference(ennf_transformation,[],[f7])).
% 1.17/0.99  
% 1.17/0.99  fof(f22,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.99    inference(flattening,[],[f21])).
% 1.17/0.99  
% 1.17/0.99  fof(f53,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f22])).
% 1.17/0.99  
% 1.17/0.99  fof(f6,axiom,(
% 1.17/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.99  
% 1.17/0.99  fof(f19,plain,(
% 1.17/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/0.99    inference(ennf_transformation,[],[f6])).
% 1.17/0.99  
% 1.17/0.99  fof(f20,plain,(
% 1.17/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.99    inference(flattening,[],[f19])).
% 1.17/0.99  
% 1.17/0.99  fof(f52,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f20])).
% 1.17/0.99  
% 1.17/0.99  fof(f59,plain,(
% 1.17/0.99    v2_pre_topc(sK2)),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f58,plain,(
% 1.17/0.99    ~v2_struct_0(sK2)),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f67,plain,(
% 1.17/0.99    ( ! [X3] : (~r2_hidden(sK3,X3) | ~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_connsp_2(sK4,sK2,sK3)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f8,axiom,(
% 1.17/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 1.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.99  
% 1.17/0.99  fof(f11,plain,(
% 1.17/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 1.17/0.99    inference(pure_predicate_removal,[],[f8])).
% 1.17/0.99  
% 1.17/0.99  fof(f23,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/0.99    inference(ennf_transformation,[],[f11])).
% 1.17/0.99  
% 1.17/0.99  fof(f24,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.99    inference(flattening,[],[f23])).
% 1.17/0.99  
% 1.17/0.99  fof(f33,plain,(
% 1.17/0.99    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_connsp_2(sK1(X0,X1,X2),X0,X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.17/0.99    introduced(choice_axiom,[])).
% 1.17/0.99  
% 1.17/0.99  fof(f34,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_connsp_2(sK1(X0,X1,X2),X0,X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f33])).
% 1.17/0.99  
% 1.17/0.99  fof(f57,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f34])).
% 1.17/0.99  
% 1.17/0.99  fof(f55,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(sK1(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f34])).
% 1.17/0.99  
% 1.17/0.99  fof(f5,axiom,(
% 1.17/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.99  
% 1.17/0.99  fof(f17,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/0.99    inference(ennf_transformation,[],[f5])).
% 1.17/0.99  
% 1.17/0.99  fof(f18,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.99    inference(flattening,[],[f17])).
% 1.17/0.99  
% 1.17/0.99  fof(f32,plain,(
% 1.17/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.99    inference(nnf_transformation,[],[f18])).
% 1.17/0.99  
% 1.17/0.99  fof(f51,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f32])).
% 1.17/0.99  
% 1.17/0.99  fof(f56,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f34])).
% 1.17/0.99  
% 1.17/0.99  fof(f54,plain,(
% 1.17/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/0.99    inference(cnf_transformation,[],[f34])).
% 1.17/0.99  
% 1.17/0.99  fof(f66,plain,(
% 1.17/0.99    r2_hidden(sK3,sK5) | m1_connsp_2(sK4,sK2,sK3)),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f65,plain,(
% 1.17/0.99    r1_tarski(sK5,sK4) | m1_connsp_2(sK4,sK2,sK3)),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f64,plain,(
% 1.17/0.99    v3_pre_topc(sK5,sK2) | m1_connsp_2(sK4,sK2,sK3)),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f63,plain,(
% 1.17/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | m1_connsp_2(sK4,sK2,sK3)),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f62,plain,(
% 1.17/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  fof(f61,plain,(
% 1.17/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.17/0.99    inference(cnf_transformation,[],[f42])).
% 1.17/0.99  
% 1.17/0.99  cnf(c_2,plain,
% 1.17/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.17/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1039,plain,
% 1.17/0.99      ( ~ r2_hidden(X0_45,X1_45)
% 1.17/0.99      | r2_hidden(X0_45,X2_45)
% 1.17/0.99      | ~ r1_tarski(X1_45,X2_45) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1236,plain,
% 1.17/0.99      ( r2_hidden(sK3,X0_45)
% 1.17/0.99      | ~ r2_hidden(sK3,sK5)
% 1.17/0.99      | ~ r1_tarski(sK5,X0_45) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1039]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1438,plain,
% 1.17/0.99      ( r2_hidden(sK3,k1_tops_1(sK2,X0_45))
% 1.17/0.99      | ~ r2_hidden(sK3,sK5)
% 1.17/0.99      | ~ r1_tarski(sK5,k1_tops_1(sK2,X0_45)) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1236]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1591,plain,
% 1.17/0.99      ( r2_hidden(sK3,k1_tops_1(sK2,sK4))
% 1.17/0.99      | ~ r2_hidden(sK3,sK5)
% 1.17/0.99      | ~ r1_tarski(sK5,k1_tops_1(sK2,sK4)) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1438]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_6,plain,
% 1.17/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.17/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | ~ r1_tarski(X0,X2)
% 1.17/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_22,negated_conjecture,
% 1.17/0.99      ( l1_pre_topc(sK2) ),
% 1.17/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_649,plain,
% 1.17/0.99      ( ~ v3_pre_topc(X0,sK2)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r1_tarski(X0,X1)
% 1.17/0.99      | r1_tarski(X0,k1_tops_1(sK2,X1)) ),
% 1.17/0.99      inference(resolution,[status(thm)],[c_6,c_22]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1020,plain,
% 1.17/0.99      ( ~ v3_pre_topc(X0_45,sK2)
% 1.17/0.99      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r1_tarski(X0_45,X1_45)
% 1.17/0.99      | r1_tarski(X0_45,k1_tops_1(sK2,X1_45)) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_649]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1228,plain,
% 1.17/0.99      ( ~ v3_pre_topc(sK5,sK2)
% 1.17/0.99      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r1_tarski(sK5,X0_45)
% 1.17/0.99      | r1_tarski(sK5,k1_tops_1(sK2,X0_45)) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1020]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1456,plain,
% 1.17/0.99      ( ~ v3_pre_topc(sK5,sK2)
% 1.17/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | r1_tarski(sK5,k1_tops_1(sK2,sK4))
% 1.17/0.99      | ~ r1_tarski(sK5,sK4) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1228]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_10,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | r2_hidden(X2,X0)
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_9,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_167,plain,
% 1.17/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | r2_hidden(X2,X0)
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_10,c_9]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_168,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | r2_hidden(X2,X0)
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_167]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_23,negated_conjecture,
% 1.17/0.99      ( v2_pre_topc(sK2) ),
% 1.17/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_473,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | r2_hidden(X1,X0)
% 1.17/0.99      | v2_struct_0(sK2)
% 1.17/0.99      | ~ l1_pre_topc(sK2) ),
% 1.17/0.99      inference(resolution,[status(thm)],[c_168,c_23]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_24,negated_conjecture,
% 1.17/0.99      ( ~ v2_struct_0(sK2) ),
% 1.17/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_477,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | r2_hidden(X1,X0) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_473,c_24,c_22]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1027,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0_45,sK2,X1_45)
% 1.17/0.99      | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
% 1.17/0.99      | r2_hidden(X1_45,X0_45) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_477]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1284,plain,
% 1.17/0.99      ( ~ m1_connsp_2(sK1(sK2,sK3,sK4),sK2,sK3)
% 1.17/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.17/0.99      | r2_hidden(sK3,sK1(sK2,sK3,sK4)) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1027]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_15,negated_conjecture,
% 1.17/0.99      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.17/0.99      | ~ v3_pre_topc(X0,sK2)
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r2_hidden(sK3,X0)
% 1.17/0.99      | ~ r1_tarski(X0,sK4) ),
% 1.17/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1035,negated_conjecture,
% 1.17/0.99      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.17/0.99      | ~ v3_pre_topc(X0_45,sK2)
% 1.17/0.99      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r2_hidden(sK3,X0_45)
% 1.17/0.99      | ~ r1_tarski(X0_45,sK4) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1193,plain,
% 1.17/0.99      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.17/0.99      | ~ v3_pre_topc(sK1(sK2,sK3,sK4),sK2)
% 1.17/0.99      | ~ m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r2_hidden(sK3,sK1(sK2,sK3,sK4))
% 1.17/0.99      | ~ r1_tarski(sK1(sK2,sK3,sK4),sK4) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1035]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_11,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | r1_tarski(sK1(X1,X2,X0),X0)
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_160,plain,
% 1.17/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | r1_tarski(sK1(X1,X2,X0),X0)
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_11,c_9]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_161,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | r1_tarski(sK1(X1,X2,X0),X0)
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_160]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_493,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | r1_tarski(sK1(sK2,X1,X0),X0)
% 1.17/0.99      | v2_struct_0(sK2)
% 1.17/0.99      | ~ l1_pre_topc(sK2) ),
% 1.17/0.99      inference(resolution,[status(thm)],[c_161,c_23]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_497,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | r1_tarski(sK1(sK2,X1,X0),X0) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_493,c_24,c_22]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1026,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0_45,sK2,X1_45)
% 1.17/0.99      | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
% 1.17/0.99      | r1_tarski(sK1(sK2,X1_45,X0_45),X0_45) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_497]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1179,plain,
% 1.17/0.99      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.17/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.17/0.99      | r1_tarski(sK1(sK2,sK3,sK4),sK4) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1026]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_13,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_146,plain,
% 1.17/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 1.17/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_13,c_9]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_147,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_146]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_533,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | m1_connsp_2(sK1(sK2,X1,X0),sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | v2_struct_0(sK2)
% 1.17/0.99      | ~ l1_pre_topc(sK2) ),
% 1.17/0.99      inference(resolution,[status(thm)],[c_147,c_23]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_537,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | m1_connsp_2(sK1(sK2,X1,X0),sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_533,c_24,c_22]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1024,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0_45,sK2,X1_45)
% 1.17/0.99      | m1_connsp_2(sK1(sK2,X1_45,X0_45),sK2,X1_45)
% 1.17/0.99      | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_537]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1176,plain,
% 1.17/0.99      ( m1_connsp_2(sK1(sK2,sK3,sK4),sK2,sK3)
% 1.17/0.99      | ~ m1_connsp_2(sK4,sK2,sK3)
% 1.17/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1024]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_7,plain,
% 1.17/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_593,plain,
% 1.17/0.99      ( m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
% 1.17/0.99      | v2_struct_0(sK2)
% 1.17/0.99      | ~ l1_pre_topc(sK2) ),
% 1.17/0.99      inference(resolution,[status(thm)],[c_7,c_23]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_597,plain,
% 1.17/0.99      ( m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_593,c_24,c_22]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1021,plain,
% 1.17/0.99      ( m1_connsp_2(X0_45,sK2,X1_45)
% 1.17/0.99      | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
% 1.17/0.99      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r2_hidden(X1_45,k1_tops_1(sK2,X0_45)) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_597]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1171,plain,
% 1.17/0.99      ( m1_connsp_2(sK4,sK2,X0_45)
% 1.17/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.17/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ r2_hidden(X0_45,k1_tops_1(sK2,sK4)) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1021]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1173,plain,
% 1.17/0.99      ( m1_connsp_2(sK4,sK2,sK3)
% 1.17/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.17/0.99      | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1171]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_12,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_153,plain,
% 1.17/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 1.17/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_12,c_9]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_154,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_153]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_513,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | v3_pre_topc(sK1(sK2,X1,X0),sK2)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | v2_struct_0(sK2)
% 1.17/0.99      | ~ l1_pre_topc(sK2) ),
% 1.17/0.99      inference(resolution,[status(thm)],[c_154,c_23]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_517,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | v3_pre_topc(sK1(sK2,X1,X0),sK2)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_513,c_24,c_22]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1025,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0_45,sK2,X1_45)
% 1.17/0.99      | v3_pre_topc(sK1(sK2,X1_45,X0_45),sK2)
% 1.17/0.99      | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
% 1.17/0.99      inference(subtyping,[status(esa)],[c_517]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_1162,plain,
% 1.17/0.99      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.17/0.99      | v3_pre_topc(sK1(sK2,sK3,sK4),sK2)
% 1.17/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.17/0.99      inference(instantiation,[status(thm)],[c_1025]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_14,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_139,plain,
% 1.17/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/0.99                [status(thm)],
% 1.17/0.99                [c_14,c_9]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_140,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/0.99      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/0.99      | v2_struct_0(X1)
% 1.17/0.99      | ~ v2_pre_topc(X1)
% 1.17/0.99      | ~ l1_pre_topc(X1) ),
% 1.17/0.99      inference(renaming,[status(thm)],[c_139]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_553,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/0.99      | v2_struct_0(sK2)
% 1.17/0.99      | ~ l1_pre_topc(sK2) ),
% 1.17/0.99      inference(resolution,[status(thm)],[c_140,c_23]) ).
% 1.17/0.99  
% 1.17/0.99  cnf(c_557,plain,
% 1.17/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/0.99      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/0.99      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_553,c_24,c_22]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1023,plain,
% 1.17/1.00      ( ~ m1_connsp_2(X0_45,sK2,X1_45)
% 1.17/1.00      | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
% 1.17/1.00      | m1_subset_1(sK1(sK2,X1_45,X0_45),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.00      inference(subtyping,[status(esa)],[c_557]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1159,plain,
% 1.17/1.00      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.17/1.00      | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1023]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_16,negated_conjecture,
% 1.17/1.00      ( m1_connsp_2(sK4,sK2,sK3) | r2_hidden(sK3,sK5) ),
% 1.17/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_17,negated_conjecture,
% 1.17/1.00      ( m1_connsp_2(sK4,sK2,sK3) | r1_tarski(sK5,sK4) ),
% 1.17/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_18,negated_conjecture,
% 1.17/1.00      ( m1_connsp_2(sK4,sK2,sK3) | v3_pre_topc(sK5,sK2) ),
% 1.17/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_19,negated_conjecture,
% 1.17/1.00      ( m1_connsp_2(sK4,sK2,sK3)
% 1.17/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_20,negated_conjecture,
% 1.17/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_21,negated_conjecture,
% 1.17/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.17/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(contradiction,plain,
% 1.17/1.00      ( $false ),
% 1.17/1.00      inference(minisat,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_1591,c_1456,c_1284,c_1193,c_1179,c_1176,c_1173,c_1162,
% 1.17/1.00                 c_1159,c_16,c_17,c_18,c_19,c_20,c_21]) ).
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.17/1.00  
% 1.17/1.00  ------                               Statistics
% 1.17/1.00  
% 1.17/1.00  ------ General
% 1.17/1.00  
% 1.17/1.00  abstr_ref_over_cycles:                  0
% 1.17/1.00  abstr_ref_under_cycles:                 0
% 1.17/1.00  gc_basic_clause_elim:                   0
% 1.17/1.00  forced_gc_time:                         0
% 1.17/1.00  parsing_time:                           0.011
% 1.17/1.00  unif_index_cands_time:                  0.
% 1.17/1.00  unif_index_add_time:                    0.
% 1.17/1.00  orderings_time:                         0.
% 1.17/1.00  out_proof_time:                         0.014
% 1.17/1.00  total_time:                             0.083
% 1.17/1.00  num_of_symbols:                         50
% 1.17/1.00  num_of_terms:                           1180
% 1.17/1.00  
% 1.17/1.00  ------ Preprocessing
% 1.17/1.00  
% 1.17/1.00  num_of_splits:                          0
% 1.17/1.00  num_of_split_atoms:                     0
% 1.17/1.00  num_of_reused_defs:                     0
% 1.17/1.00  num_eq_ax_congr_red:                    0
% 1.17/1.00  num_of_sem_filtered_clauses:            0
% 1.17/1.00  num_of_subtypes:                        2
% 1.17/1.00  monotx_restored_types:                  0
% 1.17/1.00  sat_num_of_epr_types:                   0
% 1.17/1.00  sat_num_of_non_cyclic_types:            0
% 1.17/1.00  sat_guarded_non_collapsed_types:        0
% 1.17/1.00  num_pure_diseq_elim:                    0
% 1.17/1.00  simp_replaced_by:                       0
% 1.17/1.00  res_preprocessed:                       47
% 1.17/1.00  prep_upred:                             0
% 1.17/1.00  prep_unflattend:                        0
% 1.17/1.00  smt_new_axioms:                         0
% 1.17/1.00  pred_elim_cands:                        5
% 1.17/1.00  pred_elim:                              3
% 1.17/1.00  pred_elim_cl:                           3
% 1.17/1.00  pred_elim_cycles:                       6
% 1.17/1.00  merged_defs:                            4
% 1.17/1.00  merged_defs_ncl:                        0
% 1.17/1.00  bin_hyper_res:                          4
% 1.17/1.00  prep_cycles:                            2
% 1.17/1.00  pred_elim_time:                         0.01
% 1.17/1.00  splitting_time:                         0.
% 1.17/1.00  sem_filter_time:                        0.
% 1.17/1.00  monotx_time:                            0.
% 1.17/1.00  subtype_inf_time:                       0.
% 1.17/1.00  
% 1.17/1.00  ------ Problem properties
% 1.17/1.00  
% 1.17/1.00  clauses:                                22
% 1.17/1.00  conjectures:                            7
% 1.17/1.00  epr:                                    5
% 1.17/1.00  horn:                                   17
% 1.17/1.00  ground:                                 6
% 1.17/1.00  unary:                                  2
% 1.17/1.00  binary:                                 8
% 1.17/1.00  lits:                                   59
% 1.17/1.00  lits_eq:                                0
% 1.17/1.00  fd_pure:                                0
% 1.17/1.00  fd_pseudo:                              0
% 1.17/1.00  fd_cond:                                0
% 1.17/1.00  fd_pseudo_cond:                         0
% 1.17/1.00  ac_symbols:                             0
% 1.17/1.00  
% 1.17/1.00  ------ Propositional Solver
% 1.17/1.00  
% 1.17/1.00  prop_solver_calls:                      17
% 1.17/1.00  prop_fast_solver_calls:                 509
% 1.17/1.00  smt_solver_calls:                       0
% 1.17/1.00  smt_fast_solver_calls:                  0
% 1.17/1.00  prop_num_of_clauses:                    516
% 1.17/1.00  prop_preprocess_simplified:             1934
% 1.17/1.00  prop_fo_subsumed:                       34
% 1.17/1.00  prop_solver_time:                       0.
% 1.17/1.00  smt_solver_time:                        0.
% 1.17/1.00  smt_fast_solver_time:                   0.
% 1.17/1.00  prop_fast_solver_time:                  0.
% 1.17/1.00  prop_unsat_core_time:                   0.
% 1.17/1.00  
% 1.17/1.00  ------ QBF
% 1.17/1.00  
% 1.17/1.00  qbf_q_res:                              0
% 1.17/1.00  qbf_num_tautologies:                    0
% 1.17/1.00  qbf_prep_cycles:                        0
% 1.17/1.00  
% 1.17/1.00  ------ BMC1
% 1.17/1.00  
% 1.17/1.00  bmc1_current_bound:                     -1
% 1.17/1.00  bmc1_last_solved_bound:                 -1
% 1.17/1.00  bmc1_unsat_core_size:                   -1
% 1.17/1.00  bmc1_unsat_core_parents_size:           -1
% 1.17/1.00  bmc1_merge_next_fun:                    0
% 1.17/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.17/1.00  
% 1.17/1.00  ------ Instantiation
% 1.17/1.00  
% 1.17/1.00  inst_num_of_clauses:                    115
% 1.17/1.00  inst_num_in_passive:                    32
% 1.17/1.00  inst_num_in_active:                     64
% 1.17/1.00  inst_num_in_unprocessed:                18
% 1.17/1.00  inst_num_of_loops:                      101
% 1.17/1.00  inst_num_of_learning_restarts:          0
% 1.17/1.00  inst_num_moves_active_passive:          33
% 1.17/1.00  inst_lit_activity:                      0
% 1.17/1.00  inst_lit_activity_moves:                0
% 1.17/1.00  inst_num_tautologies:                   0
% 1.17/1.00  inst_num_prop_implied:                  0
% 1.17/1.00  inst_num_existing_simplified:           0
% 1.17/1.00  inst_num_eq_res_simplified:             0
% 1.17/1.00  inst_num_child_elim:                    0
% 1.17/1.00  inst_num_of_dismatching_blockings:      19
% 1.17/1.00  inst_num_of_non_proper_insts:           68
% 1.17/1.00  inst_num_of_duplicates:                 0
% 1.17/1.00  inst_inst_num_from_inst_to_res:         0
% 1.17/1.00  inst_dismatching_checking_time:         0.
% 1.17/1.00  
% 1.17/1.00  ------ Resolution
% 1.17/1.00  
% 1.17/1.00  res_num_of_clauses:                     0
% 1.17/1.00  res_num_in_passive:                     0
% 1.17/1.00  res_num_in_active:                      0
% 1.17/1.00  res_num_of_loops:                       49
% 1.17/1.00  res_forward_subset_subsumed:            4
% 1.17/1.00  res_backward_subset_subsumed:           0
% 1.17/1.00  res_forward_subsumed:                   0
% 1.17/1.00  res_backward_subsumed:                  0
% 1.17/1.00  res_forward_subsumption_resolution:     0
% 1.17/1.00  res_backward_subsumption_resolution:    0
% 1.17/1.00  res_clause_to_clause_subsumption:       81
% 1.17/1.00  res_orphan_elimination:                 0
% 1.17/1.00  res_tautology_del:                      12
% 1.17/1.00  res_num_eq_res_simplified:              0
% 1.17/1.00  res_num_sel_changes:                    0
% 1.17/1.00  res_moves_from_active_to_pass:          0
% 1.17/1.00  
% 1.17/1.00  ------ Superposition
% 1.17/1.00  
% 1.17/1.00  sup_time_total:                         0.
% 1.17/1.00  sup_time_generating:                    0.
% 1.17/1.00  sup_time_sim_full:                      0.
% 1.17/1.00  sup_time_sim_immed:                     0.
% 1.17/1.00  
% 1.17/1.00  sup_num_of_clauses:                     0
% 1.17/1.00  sup_num_in_active:                      0
% 1.17/1.00  sup_num_in_passive:                     0
% 1.17/1.00  sup_num_of_loops:                       0
% 1.17/1.00  sup_fw_superposition:                   0
% 1.17/1.00  sup_bw_superposition:                   0
% 1.17/1.00  sup_immediate_simplified:               0
% 1.17/1.00  sup_given_eliminated:                   0
% 1.17/1.00  comparisons_done:                       0
% 1.17/1.00  comparisons_avoided:                    0
% 1.17/1.00  
% 1.17/1.00  ------ Simplifications
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  sim_fw_subset_subsumed:                 0
% 1.17/1.00  sim_bw_subset_subsumed:                 0
% 1.17/1.00  sim_fw_subsumed:                        0
% 1.17/1.00  sim_bw_subsumed:                        0
% 1.17/1.00  sim_fw_subsumption_res:                 0
% 1.17/1.00  sim_bw_subsumption_res:                 0
% 1.17/1.00  sim_tautology_del:                      0
% 1.17/1.00  sim_eq_tautology_del:                   0
% 1.17/1.00  sim_eq_res_simp:                        0
% 1.17/1.00  sim_fw_demodulated:                     0
% 1.17/1.00  sim_bw_demodulated:                     0
% 1.17/1.00  sim_light_normalised:                   0
% 1.17/1.00  sim_joinable_taut:                      0
% 1.17/1.00  sim_joinable_simp:                      0
% 1.17/1.00  sim_ac_normalised:                      0
% 1.17/1.00  sim_smt_subsumption:                    0
% 1.17/1.00  
%------------------------------------------------------------------------------
