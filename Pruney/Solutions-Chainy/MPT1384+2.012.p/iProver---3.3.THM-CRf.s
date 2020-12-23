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
% DateTime   : Thu Dec  3 12:18:26 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 887 expanded)
%              Number of clauses        :  114 ( 201 expanded)
%              Number of leaves         :   16 ( 252 expanded)
%              Depth                    :   23
%              Number of atoms          :  875 (9351 expanded)
%              Number of equality atoms :   93 ( 193 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,X0,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f48,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK5(X4),X1)
        & m1_connsp_2(sK5(X4),X0,X4)
        & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK4)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,X0,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,sK3)
                  | ~ m1_connsp_2(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,sK3)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK3,X0) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( r1_tarski(X5,sK3)
                  & m1_connsp_2(X5,X0,X4)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,sK3)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v3_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,sK2,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK2)) )
            | ~ v3_pre_topc(X1,sK2) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,sK2,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            | v3_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ( ! [X3] :
            ( ~ r1_tarski(X3,sK3)
            | ~ m1_connsp_2(X3,sK2,sK4)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & r2_hidden(sK4,sK3)
        & m1_subset_1(sK4,u1_struct_0(sK2)) )
      | ~ v3_pre_topc(sK3,sK2) )
    & ( ! [X4] :
          ( ( r1_tarski(sK5(X4),sK3)
            & m1_connsp_2(sK5(X4),sK2,X4)
            & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2))) )
          | ~ r2_hidden(X4,sK3)
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f44,f48,f47,f46,f45])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | ~ m1_connsp_2(X3,sK2,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f11,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f34])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X4] :
      ( m1_connsp_2(sK5(X4),sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X4] :
      ( r1_tarski(sK5(X4),sK3)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_239,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_240,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_303,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_240])).

cnf(c_4552,plain,
    ( r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),X0)
    | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))))
    | ~ r1_tarski(k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))),X0) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_13353,plain,
    ( ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))))
    | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
    | ~ r1_tarski(k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4552])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_724,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK2,X0),k1_tops_1(sK2,X1)) ),
    inference(unflattening,[status(thm)],[c_724])).

cnf(c_4394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,X0))
    | ~ r1_tarski(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),X0) ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_7390,plain,
    ( ~ m1_subset_1(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,sK3))
    | ~ r1_tarski(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_4394])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2940,plain,
    ( m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4319,plain,
    ( m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_2940])).

cnf(c_22,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK2,sK4)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_19,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_468,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_469,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_473,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_30,c_29])).

cnf(c_815,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X2))
    | ~ r1_tarski(X1,sK3)
    | X2 != X1
    | sK4 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_473])).

cnf(c_816,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,k1_tops_1(sK2,X0))
    | ~ r1_tarski(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_815])).

cnf(c_24,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_820,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK3,sK2)
    | ~ r2_hidden(sK4,k1_tops_1(sK2,X0))
    | ~ r1_tarski(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_816,c_24])).

cnf(c_821,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,k1_tops_1(sK2,X0))
    | ~ r1_tarski(X0,sK3) ),
    inference(renaming,[status(thm)],[c_820])).

cnf(c_1795,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,k1_tops_1(sK2,X0)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_46,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2175,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2178,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2175])).

cnf(c_21,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_415,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_416,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_420,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_30,c_29])).

cnf(c_436,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_420,c_9])).

cnf(c_839,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X0)
    | ~ r1_tarski(X1,sK3)
    | X0 != X1
    | sK4 != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_436])).

cnf(c_840,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,X0)
    | ~ r1_tarski(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_2849,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,sK3)
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_2850,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2849])).

cnf(c_3275,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1795,c_35,c_46,c_2178,c_2850])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0,X2),X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X0)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_240])).

cnf(c_993,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_994,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_993])).

cnf(c_1046,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_304,c_994])).

cnf(c_2182,plain,
    ( ~ r2_hidden(sK0(X0,sK3,X1),X1)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2384,plain,
    ( ~ r2_hidden(sK0(sK3,sK3,X0),X0)
    | ~ r1_tarski(X0,sK3)
    | r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_3270,plain,
    ( ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_26,negated_conjecture,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_444,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_445,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_449,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_30,c_29])).

cnf(c_860,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r2_hidden(X0,sK3)
    | X1 != X0
    | sK5(X0) != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_449])).

cnf(c_861,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_860])).

cnf(c_27,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_865,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v3_pre_topc(sK3,sK2)
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_861,c_27])).

cnf(c_866,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_865])).

cnf(c_2945,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))))
    | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_2946,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | m1_subset_1(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK5(X0),sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2947,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3)
    | r1_tarski(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1811,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_646,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_647,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_651,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_29])).

cnf(c_652,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_651])).

cnf(c_706,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(X1,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_652,c_29])).

cnf(c_707,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_1144,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_707])).

cnf(c_1803,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_1145,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_707])).

cnf(c_1181,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_1182,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_17,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_528,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_529,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_533,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_529,c_29])).

cnf(c_534,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_533])).

cnf(c_754,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_534])).

cnf(c_755,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_1141,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_755])).

cnf(c_1799,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(c_2131,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1811,c_1799])).

cnf(c_2779,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | k1_tops_1(sK2,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1803,c_1181,c_1182,c_2131])).

cnf(c_2780,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2779])).

cnf(c_2789,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1811,c_2780])).

cnf(c_2827,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2789])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X0,X2),X0)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X2,X0),X2)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_240])).

cnf(c_1047,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_305,c_994])).

cnf(c_2181,plain,
    ( r2_hidden(sK0(X0,sK3,X1),sK3)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_2299,plain,
    ( r2_hidden(sK0(sK3,sK3,X0),sK3)
    | ~ r1_tarski(X0,sK3)
    | r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2181])).

cnf(c_2513,plain,
    ( r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3)
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2143,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1142,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_755])).

cnf(c_1143,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_755])).

cnf(c_1248,plain,
    ( k1_tops_1(sK2,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1142,c_1143,c_1141])).

cnf(c_1249,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_1248])).

cnf(c_2073,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_2074,plain,
    ( k1_tops_1(sK2,sK3) != sK3
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2073])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_742,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_2070,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13353,c_7390,c_4319,c_3275,c_3270,c_2945,c_2946,c_2947,c_2827,c_2513,c_2175,c_2143,c_2074,c_2070,c_35,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:23:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.51/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/0.97  
% 3.51/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.97  
% 3.51/0.97  ------  iProver source info
% 3.51/0.97  
% 3.51/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.97  git: non_committed_changes: false
% 3.51/0.97  git: last_make_outside_of_git: false
% 3.51/0.97  
% 3.51/0.97  ------ 
% 3.51/0.97  
% 3.51/0.97  ------ Input Options
% 3.51/0.97  
% 3.51/0.97  --out_options                           all
% 3.51/0.97  --tptp_safe_out                         true
% 3.51/0.97  --problem_path                          ""
% 3.51/0.97  --include_path                          ""
% 3.51/0.97  --clausifier                            res/vclausify_rel
% 3.51/0.97  --clausifier_options                    --mode clausify
% 3.51/0.97  --stdin                                 false
% 3.51/0.97  --stats_out                             all
% 3.51/0.97  
% 3.51/0.97  ------ General Options
% 3.51/0.97  
% 3.51/0.97  --fof                                   false
% 3.51/0.97  --time_out_real                         305.
% 3.51/0.97  --time_out_virtual                      -1.
% 3.51/0.97  --symbol_type_check                     false
% 3.51/0.97  --clausify_out                          false
% 3.51/0.97  --sig_cnt_out                           false
% 3.51/0.97  --trig_cnt_out                          false
% 3.51/0.97  --trig_cnt_out_tolerance                1.
% 3.51/0.97  --trig_cnt_out_sk_spl                   false
% 3.51/0.97  --abstr_cl_out                          false
% 3.51/0.97  
% 3.51/0.97  ------ Global Options
% 3.51/0.97  
% 3.51/0.97  --schedule                              default
% 3.51/0.97  --add_important_lit                     false
% 3.51/0.97  --prop_solver_per_cl                    1000
% 3.51/0.97  --min_unsat_core                        false
% 3.51/0.97  --soft_assumptions                      false
% 3.51/0.97  --soft_lemma_size                       3
% 3.51/0.97  --prop_impl_unit_size                   0
% 3.51/0.97  --prop_impl_unit                        []
% 3.51/0.97  --share_sel_clauses                     true
% 3.51/0.97  --reset_solvers                         false
% 3.51/0.97  --bc_imp_inh                            [conj_cone]
% 3.51/0.97  --conj_cone_tolerance                   3.
% 3.51/0.97  --extra_neg_conj                        none
% 3.51/0.97  --large_theory_mode                     true
% 3.51/0.97  --prolific_symb_bound                   200
% 3.51/0.97  --lt_threshold                          2000
% 3.51/0.97  --clause_weak_htbl                      true
% 3.51/0.97  --gc_record_bc_elim                     false
% 3.51/0.97  
% 3.51/0.97  ------ Preprocessing Options
% 3.51/0.97  
% 3.51/0.97  --preprocessing_flag                    true
% 3.51/0.97  --time_out_prep_mult                    0.1
% 3.51/0.97  --splitting_mode                        input
% 3.51/0.97  --splitting_grd                         true
% 3.51/0.97  --splitting_cvd                         false
% 3.51/0.97  --splitting_cvd_svl                     false
% 3.51/0.97  --splitting_nvd                         32
% 3.51/0.97  --sub_typing                            true
% 3.51/0.97  --prep_gs_sim                           true
% 3.51/0.97  --prep_unflatten                        true
% 3.51/0.97  --prep_res_sim                          true
% 3.51/0.97  --prep_upred                            true
% 3.51/0.97  --prep_sem_filter                       exhaustive
% 3.51/0.97  --prep_sem_filter_out                   false
% 3.51/0.97  --pred_elim                             true
% 3.51/0.97  --res_sim_input                         true
% 3.51/0.97  --eq_ax_congr_red                       true
% 3.51/0.97  --pure_diseq_elim                       true
% 3.51/0.97  --brand_transform                       false
% 3.51/0.97  --non_eq_to_eq                          false
% 3.51/0.97  --prep_def_merge                        true
% 3.51/0.97  --prep_def_merge_prop_impl              false
% 3.51/0.97  --prep_def_merge_mbd                    true
% 3.51/0.97  --prep_def_merge_tr_red                 false
% 3.51/0.97  --prep_def_merge_tr_cl                  false
% 3.51/0.97  --smt_preprocessing                     true
% 3.51/0.97  --smt_ac_axioms                         fast
% 3.51/0.97  --preprocessed_out                      false
% 3.51/0.97  --preprocessed_stats                    false
% 3.51/0.97  
% 3.51/0.97  ------ Abstraction refinement Options
% 3.51/0.97  
% 3.51/0.97  --abstr_ref                             []
% 3.51/0.97  --abstr_ref_prep                        false
% 3.51/0.97  --abstr_ref_until_sat                   false
% 3.51/0.97  --abstr_ref_sig_restrict                funpre
% 3.51/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.97  --abstr_ref_under                       []
% 3.51/0.97  
% 3.51/0.97  ------ SAT Options
% 3.51/0.97  
% 3.51/0.97  --sat_mode                              false
% 3.51/0.97  --sat_fm_restart_options                ""
% 3.51/0.97  --sat_gr_def                            false
% 3.51/0.97  --sat_epr_types                         true
% 3.51/0.97  --sat_non_cyclic_types                  false
% 3.51/0.97  --sat_finite_models                     false
% 3.51/0.97  --sat_fm_lemmas                         false
% 3.51/0.97  --sat_fm_prep                           false
% 3.51/0.97  --sat_fm_uc_incr                        true
% 3.51/0.97  --sat_out_model                         small
% 3.51/0.97  --sat_out_clauses                       false
% 3.51/0.97  
% 3.51/0.97  ------ QBF Options
% 3.51/0.97  
% 3.51/0.97  --qbf_mode                              false
% 3.51/0.97  --qbf_elim_univ                         false
% 3.51/0.97  --qbf_dom_inst                          none
% 3.51/0.97  --qbf_dom_pre_inst                      false
% 3.51/0.97  --qbf_sk_in                             false
% 3.51/0.97  --qbf_pred_elim                         true
% 3.51/0.97  --qbf_split                             512
% 3.51/0.97  
% 3.51/0.97  ------ BMC1 Options
% 3.51/0.97  
% 3.51/0.97  --bmc1_incremental                      false
% 3.51/0.97  --bmc1_axioms                           reachable_all
% 3.51/0.97  --bmc1_min_bound                        0
% 3.51/0.97  --bmc1_max_bound                        -1
% 3.51/0.97  --bmc1_max_bound_default                -1
% 3.51/0.97  --bmc1_symbol_reachability              true
% 3.51/0.97  --bmc1_property_lemmas                  false
% 3.51/0.97  --bmc1_k_induction                      false
% 3.51/0.97  --bmc1_non_equiv_states                 false
% 3.51/0.97  --bmc1_deadlock                         false
% 3.51/0.97  --bmc1_ucm                              false
% 3.51/0.97  --bmc1_add_unsat_core                   none
% 3.51/0.97  --bmc1_unsat_core_children              false
% 3.51/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.97  --bmc1_out_stat                         full
% 3.51/0.97  --bmc1_ground_init                      false
% 3.51/0.97  --bmc1_pre_inst_next_state              false
% 3.51/0.97  --bmc1_pre_inst_state                   false
% 3.51/0.97  --bmc1_pre_inst_reach_state             false
% 3.51/0.97  --bmc1_out_unsat_core                   false
% 3.51/0.97  --bmc1_aig_witness_out                  false
% 3.51/0.97  --bmc1_verbose                          false
% 3.51/0.97  --bmc1_dump_clauses_tptp                false
% 3.51/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.97  --bmc1_dump_file                        -
% 3.51/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.97  --bmc1_ucm_extend_mode                  1
% 3.51/0.97  --bmc1_ucm_init_mode                    2
% 3.51/0.97  --bmc1_ucm_cone_mode                    none
% 3.51/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.97  --bmc1_ucm_relax_model                  4
% 3.51/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.97  --bmc1_ucm_layered_model                none
% 3.51/0.97  --bmc1_ucm_max_lemma_size               10
% 3.51/0.97  
% 3.51/0.97  ------ AIG Options
% 3.51/0.97  
% 3.51/0.97  --aig_mode                              false
% 3.51/0.97  
% 3.51/0.97  ------ Instantiation Options
% 3.51/0.97  
% 3.51/0.97  --instantiation_flag                    true
% 3.51/0.97  --inst_sos_flag                         false
% 3.51/0.97  --inst_sos_phase                        true
% 3.51/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.97  --inst_lit_sel_side                     num_symb
% 3.51/0.97  --inst_solver_per_active                1400
% 3.51/0.97  --inst_solver_calls_frac                1.
% 3.51/0.97  --inst_passive_queue_type               priority_queues
% 3.51/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.97  --inst_passive_queues_freq              [25;2]
% 3.51/0.97  --inst_dismatching                      true
% 3.51/0.97  --inst_eager_unprocessed_to_passive     true
% 3.51/0.97  --inst_prop_sim_given                   true
% 3.51/0.97  --inst_prop_sim_new                     false
% 3.51/0.97  --inst_subs_new                         false
% 3.51/0.97  --inst_eq_res_simp                      false
% 3.51/0.97  --inst_subs_given                       false
% 3.51/0.97  --inst_orphan_elimination               true
% 3.51/0.97  --inst_learning_loop_flag               true
% 3.51/0.97  --inst_learning_start                   3000
% 3.51/0.97  --inst_learning_factor                  2
% 3.51/0.97  --inst_start_prop_sim_after_learn       3
% 3.51/0.97  --inst_sel_renew                        solver
% 3.51/0.97  --inst_lit_activity_flag                true
% 3.51/0.97  --inst_restr_to_given                   false
% 3.51/0.97  --inst_activity_threshold               500
% 3.51/0.97  --inst_out_proof                        true
% 3.51/0.97  
% 3.51/0.97  ------ Resolution Options
% 3.51/0.97  
% 3.51/0.97  --resolution_flag                       true
% 3.51/0.97  --res_lit_sel                           adaptive
% 3.51/0.97  --res_lit_sel_side                      none
% 3.51/0.97  --res_ordering                          kbo
% 3.51/0.97  --res_to_prop_solver                    active
% 3.51/0.97  --res_prop_simpl_new                    false
% 3.51/0.97  --res_prop_simpl_given                  true
% 3.51/0.97  --res_passive_queue_type                priority_queues
% 3.51/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.97  --res_passive_queues_freq               [15;5]
% 3.51/0.97  --res_forward_subs                      full
% 3.51/0.97  --res_backward_subs                     full
% 3.51/0.97  --res_forward_subs_resolution           true
% 3.51/0.97  --res_backward_subs_resolution          true
% 3.51/0.97  --res_orphan_elimination                true
% 3.51/0.97  --res_time_limit                        2.
% 3.51/0.97  --res_out_proof                         true
% 3.51/0.97  
% 3.51/0.97  ------ Superposition Options
% 3.51/0.97  
% 3.51/0.97  --superposition_flag                    true
% 3.51/0.97  --sup_passive_queue_type                priority_queues
% 3.51/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.97  --demod_completeness_check              fast
% 3.51/0.97  --demod_use_ground                      true
% 3.51/0.97  --sup_to_prop_solver                    passive
% 3.51/0.97  --sup_prop_simpl_new                    true
% 3.51/0.97  --sup_prop_simpl_given                  true
% 3.51/0.97  --sup_fun_splitting                     false
% 3.51/0.97  --sup_smt_interval                      50000
% 3.51/0.97  
% 3.51/0.97  ------ Superposition Simplification Setup
% 3.51/0.97  
% 3.51/0.97  --sup_indices_passive                   []
% 3.51/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.97  --sup_full_bw                           [BwDemod]
% 3.51/0.97  --sup_immed_triv                        [TrivRules]
% 3.51/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.97  --sup_immed_bw_main                     []
% 3.51/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.97  
% 3.51/0.97  ------ Combination Options
% 3.51/0.97  
% 3.51/0.97  --comb_res_mult                         3
% 3.51/0.97  --comb_sup_mult                         2
% 3.51/0.97  --comb_inst_mult                        10
% 3.51/0.97  
% 3.51/0.97  ------ Debug Options
% 3.51/0.97  
% 3.51/0.97  --dbg_backtrace                         false
% 3.51/0.97  --dbg_dump_prop_clauses                 false
% 3.51/0.97  --dbg_dump_prop_clauses_file            -
% 3.51/0.97  --dbg_out_stat                          false
% 3.51/0.97  ------ Parsing...
% 3.51/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.97  
% 3.51/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.51/0.97  
% 3.51/0.97  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.97  
% 3.51/0.97  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.97  ------ Proving...
% 3.51/0.97  ------ Problem Properties 
% 3.51/0.97  
% 3.51/0.97  
% 3.51/0.97  clauses                                 31
% 3.51/0.97  conjectures                             5
% 3.51/0.97  EPR                                     6
% 3.51/0.97  Horn                                    24
% 3.51/0.97  unary                                   2
% 3.51/0.97  binary                                  9
% 3.51/0.97  lits                                    96
% 3.51/0.97  lits eq                                 3
% 3.51/0.97  fd_pure                                 0
% 3.51/0.97  fd_pseudo                               0
% 3.51/0.97  fd_cond                                 0
% 3.51/0.97  fd_pseudo_cond                          1
% 3.51/0.97  AC symbols                              0
% 3.51/0.97  
% 3.51/0.97  ------ Schedule dynamic 5 is on 
% 3.51/0.97  
% 3.51/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.97  
% 3.51/0.97  
% 3.51/0.97  ------ 
% 3.51/0.97  Current options:
% 3.51/0.97  ------ 
% 3.51/0.97  
% 3.51/0.97  ------ Input Options
% 3.51/0.97  
% 3.51/0.97  --out_options                           all
% 3.51/0.97  --tptp_safe_out                         true
% 3.51/0.97  --problem_path                          ""
% 3.51/0.97  --include_path                          ""
% 3.51/0.97  --clausifier                            res/vclausify_rel
% 3.51/0.97  --clausifier_options                    --mode clausify
% 3.51/0.97  --stdin                                 false
% 3.51/0.97  --stats_out                             all
% 3.51/0.97  
% 3.51/0.97  ------ General Options
% 3.51/0.97  
% 3.51/0.97  --fof                                   false
% 3.51/0.97  --time_out_real                         305.
% 3.51/0.97  --time_out_virtual                      -1.
% 3.51/0.97  --symbol_type_check                     false
% 3.51/0.97  --clausify_out                          false
% 3.51/0.97  --sig_cnt_out                           false
% 3.51/0.97  --trig_cnt_out                          false
% 3.51/0.97  --trig_cnt_out_tolerance                1.
% 3.51/0.97  --trig_cnt_out_sk_spl                   false
% 3.51/0.97  --abstr_cl_out                          false
% 3.51/0.97  
% 3.51/0.97  ------ Global Options
% 3.51/0.97  
% 3.51/0.97  --schedule                              default
% 3.51/0.97  --add_important_lit                     false
% 3.51/0.97  --prop_solver_per_cl                    1000
% 3.51/0.97  --min_unsat_core                        false
% 3.51/0.97  --soft_assumptions                      false
% 3.51/0.97  --soft_lemma_size                       3
% 3.51/0.97  --prop_impl_unit_size                   0
% 3.51/0.97  --prop_impl_unit                        []
% 3.51/0.97  --share_sel_clauses                     true
% 3.51/0.97  --reset_solvers                         false
% 3.51/0.97  --bc_imp_inh                            [conj_cone]
% 3.51/0.97  --conj_cone_tolerance                   3.
% 3.51/0.97  --extra_neg_conj                        none
% 3.51/0.97  --large_theory_mode                     true
% 3.51/0.97  --prolific_symb_bound                   200
% 3.51/0.97  --lt_threshold                          2000
% 3.51/0.97  --clause_weak_htbl                      true
% 3.51/0.97  --gc_record_bc_elim                     false
% 3.51/0.97  
% 3.51/0.97  ------ Preprocessing Options
% 3.51/0.97  
% 3.51/0.97  --preprocessing_flag                    true
% 3.51/0.97  --time_out_prep_mult                    0.1
% 3.51/0.97  --splitting_mode                        input
% 3.51/0.97  --splitting_grd                         true
% 3.51/0.97  --splitting_cvd                         false
% 3.51/0.97  --splitting_cvd_svl                     false
% 3.51/0.97  --splitting_nvd                         32
% 3.51/0.97  --sub_typing                            true
% 3.51/0.97  --prep_gs_sim                           true
% 3.51/0.97  --prep_unflatten                        true
% 3.51/0.97  --prep_res_sim                          true
% 3.51/0.97  --prep_upred                            true
% 3.51/0.97  --prep_sem_filter                       exhaustive
% 3.51/0.97  --prep_sem_filter_out                   false
% 3.51/0.97  --pred_elim                             true
% 3.51/0.97  --res_sim_input                         true
% 3.51/0.97  --eq_ax_congr_red                       true
% 3.51/0.97  --pure_diseq_elim                       true
% 3.51/0.97  --brand_transform                       false
% 3.51/0.97  --non_eq_to_eq                          false
% 3.51/0.97  --prep_def_merge                        true
% 3.51/0.97  --prep_def_merge_prop_impl              false
% 3.51/0.97  --prep_def_merge_mbd                    true
% 3.51/0.97  --prep_def_merge_tr_red                 false
% 3.51/0.97  --prep_def_merge_tr_cl                  false
% 3.51/0.97  --smt_preprocessing                     true
% 3.51/0.97  --smt_ac_axioms                         fast
% 3.51/0.97  --preprocessed_out                      false
% 3.51/0.97  --preprocessed_stats                    false
% 3.51/0.97  
% 3.51/0.97  ------ Abstraction refinement Options
% 3.51/0.97  
% 3.51/0.97  --abstr_ref                             []
% 3.51/0.97  --abstr_ref_prep                        false
% 3.51/0.97  --abstr_ref_until_sat                   false
% 3.51/0.97  --abstr_ref_sig_restrict                funpre
% 3.51/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.97  --abstr_ref_under                       []
% 3.51/0.97  
% 3.51/0.97  ------ SAT Options
% 3.51/0.97  
% 3.51/0.97  --sat_mode                              false
% 3.51/0.97  --sat_fm_restart_options                ""
% 3.51/0.97  --sat_gr_def                            false
% 3.51/0.97  --sat_epr_types                         true
% 3.51/0.97  --sat_non_cyclic_types                  false
% 3.51/0.97  --sat_finite_models                     false
% 3.51/0.97  --sat_fm_lemmas                         false
% 3.51/0.97  --sat_fm_prep                           false
% 3.51/0.97  --sat_fm_uc_incr                        true
% 3.51/0.97  --sat_out_model                         small
% 3.51/0.97  --sat_out_clauses                       false
% 3.51/0.97  
% 3.51/0.97  ------ QBF Options
% 3.51/0.97  
% 3.51/0.97  --qbf_mode                              false
% 3.51/0.97  --qbf_elim_univ                         false
% 3.51/0.97  --qbf_dom_inst                          none
% 3.51/0.97  --qbf_dom_pre_inst                      false
% 3.51/0.97  --qbf_sk_in                             false
% 3.51/0.97  --qbf_pred_elim                         true
% 3.51/0.97  --qbf_split                             512
% 3.51/0.97  
% 3.51/0.97  ------ BMC1 Options
% 3.51/0.97  
% 3.51/0.97  --bmc1_incremental                      false
% 3.51/0.97  --bmc1_axioms                           reachable_all
% 3.51/0.97  --bmc1_min_bound                        0
% 3.51/0.97  --bmc1_max_bound                        -1
% 3.51/0.97  --bmc1_max_bound_default                -1
% 3.51/0.97  --bmc1_symbol_reachability              true
% 3.51/0.97  --bmc1_property_lemmas                  false
% 3.51/0.97  --bmc1_k_induction                      false
% 3.51/0.97  --bmc1_non_equiv_states                 false
% 3.51/0.97  --bmc1_deadlock                         false
% 3.51/0.97  --bmc1_ucm                              false
% 3.51/0.97  --bmc1_add_unsat_core                   none
% 3.51/0.97  --bmc1_unsat_core_children              false
% 3.51/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.97  --bmc1_out_stat                         full
% 3.51/0.97  --bmc1_ground_init                      false
% 3.51/0.97  --bmc1_pre_inst_next_state              false
% 3.51/0.97  --bmc1_pre_inst_state                   false
% 3.51/0.97  --bmc1_pre_inst_reach_state             false
% 3.51/0.97  --bmc1_out_unsat_core                   false
% 3.51/0.97  --bmc1_aig_witness_out                  false
% 3.51/0.97  --bmc1_verbose                          false
% 3.51/0.97  --bmc1_dump_clauses_tptp                false
% 3.51/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.97  --bmc1_dump_file                        -
% 3.51/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.97  --bmc1_ucm_extend_mode                  1
% 3.51/0.97  --bmc1_ucm_init_mode                    2
% 3.51/0.97  --bmc1_ucm_cone_mode                    none
% 3.51/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.97  --bmc1_ucm_relax_model                  4
% 3.51/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.97  --bmc1_ucm_layered_model                none
% 3.51/0.97  --bmc1_ucm_max_lemma_size               10
% 3.51/0.97  
% 3.51/0.97  ------ AIG Options
% 3.51/0.97  
% 3.51/0.97  --aig_mode                              false
% 3.51/0.97  
% 3.51/0.97  ------ Instantiation Options
% 3.51/0.97  
% 3.51/0.97  --instantiation_flag                    true
% 3.51/0.97  --inst_sos_flag                         false
% 3.51/0.97  --inst_sos_phase                        true
% 3.51/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.97  --inst_lit_sel_side                     none
% 3.51/0.97  --inst_solver_per_active                1400
% 3.51/0.97  --inst_solver_calls_frac                1.
% 3.51/0.97  --inst_passive_queue_type               priority_queues
% 3.51/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.97  --inst_passive_queues_freq              [25;2]
% 3.51/0.97  --inst_dismatching                      true
% 3.51/0.97  --inst_eager_unprocessed_to_passive     true
% 3.51/0.97  --inst_prop_sim_given                   true
% 3.51/0.97  --inst_prop_sim_new                     false
% 3.51/0.97  --inst_subs_new                         false
% 3.51/0.97  --inst_eq_res_simp                      false
% 3.51/0.97  --inst_subs_given                       false
% 3.51/0.97  --inst_orphan_elimination               true
% 3.51/0.97  --inst_learning_loop_flag               true
% 3.51/0.97  --inst_learning_start                   3000
% 3.51/0.97  --inst_learning_factor                  2
% 3.51/0.97  --inst_start_prop_sim_after_learn       3
% 3.51/0.97  --inst_sel_renew                        solver
% 3.51/0.97  --inst_lit_activity_flag                true
% 3.51/0.97  --inst_restr_to_given                   false
% 3.51/0.97  --inst_activity_threshold               500
% 3.51/0.97  --inst_out_proof                        true
% 3.51/0.97  
% 3.51/0.97  ------ Resolution Options
% 3.51/0.97  
% 3.51/0.97  --resolution_flag                       false
% 3.51/0.97  --res_lit_sel                           adaptive
% 3.51/0.97  --res_lit_sel_side                      none
% 3.51/0.97  --res_ordering                          kbo
% 3.51/0.97  --res_to_prop_solver                    active
% 3.51/0.97  --res_prop_simpl_new                    false
% 3.51/0.97  --res_prop_simpl_given                  true
% 3.51/0.97  --res_passive_queue_type                priority_queues
% 3.51/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.97  --res_passive_queues_freq               [15;5]
% 3.51/0.97  --res_forward_subs                      full
% 3.51/0.97  --res_backward_subs                     full
% 3.51/0.97  --res_forward_subs_resolution           true
% 3.51/0.97  --res_backward_subs_resolution          true
% 3.51/0.97  --res_orphan_elimination                true
% 3.51/0.97  --res_time_limit                        2.
% 3.51/0.97  --res_out_proof                         true
% 3.51/0.97  
% 3.51/0.97  ------ Superposition Options
% 3.51/0.97  
% 3.51/0.97  --superposition_flag                    true
% 3.51/0.97  --sup_passive_queue_type                priority_queues
% 3.51/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.97  --demod_completeness_check              fast
% 3.51/0.97  --demod_use_ground                      true
% 3.51/0.97  --sup_to_prop_solver                    passive
% 3.51/0.97  --sup_prop_simpl_new                    true
% 3.51/0.97  --sup_prop_simpl_given                  true
% 3.51/0.97  --sup_fun_splitting                     false
% 3.51/0.97  --sup_smt_interval                      50000
% 3.51/0.97  
% 3.51/0.97  ------ Superposition Simplification Setup
% 3.51/0.97  
% 3.51/0.97  --sup_indices_passive                   []
% 3.51/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.97  --sup_full_bw                           [BwDemod]
% 3.51/0.97  --sup_immed_triv                        [TrivRules]
% 3.51/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.97  --sup_immed_bw_main                     []
% 3.51/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.97  
% 3.51/0.97  ------ Combination Options
% 3.51/0.97  
% 3.51/0.97  --comb_res_mult                         3
% 3.51/0.97  --comb_sup_mult                         2
% 3.51/0.97  --comb_inst_mult                        10
% 3.51/0.97  
% 3.51/0.97  ------ Debug Options
% 3.51/0.97  
% 3.51/0.97  --dbg_backtrace                         false
% 3.51/0.97  --dbg_dump_prop_clauses                 false
% 3.51/0.97  --dbg_dump_prop_clauses_file            -
% 3.51/0.97  --dbg_out_stat                          false
% 3.51/0.97  
% 3.51/0.97  
% 3.51/0.97  
% 3.51/0.97  
% 3.51/0.97  ------ Proving...
% 3.51/0.97  
% 3.51/0.97  
% 3.51/0.97  % SZS status Theorem for theBenchmark.p
% 3.51/0.97  
% 3.51/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/0.97  
% 3.51/0.97  fof(f2,axiom,(
% 3.51/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f14,plain,(
% 3.51/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.97    inference(ennf_transformation,[],[f2])).
% 3.51/0.97  
% 3.51/0.97  fof(f53,plain,(
% 3.51/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.97    inference(cnf_transformation,[],[f14])).
% 3.51/0.97  
% 3.51/0.97  fof(f4,axiom,(
% 3.51/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f36,plain,(
% 3.51/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.51/0.97    inference(nnf_transformation,[],[f4])).
% 3.51/0.97  
% 3.51/0.97  fof(f58,plain,(
% 3.51/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f36])).
% 3.51/0.97  
% 3.51/0.97  fof(f7,axiom,(
% 3.51/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f20,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.97    inference(ennf_transformation,[],[f7])).
% 3.51/0.97  
% 3.51/0.97  fof(f21,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.97    inference(flattening,[],[f20])).
% 3.51/0.97  
% 3.51/0.97  fof(f61,plain,(
% 3.51/0.97    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f21])).
% 3.51/0.97  
% 3.51/0.97  fof(f12,conjecture,(
% 3.51/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f13,negated_conjecture,(
% 3.51/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.51/0.97    inference(negated_conjecture,[],[f12])).
% 3.51/0.97  
% 3.51/0.97  fof(f30,plain,(
% 3.51/0.97    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.51/0.97    inference(ennf_transformation,[],[f13])).
% 3.51/0.97  
% 3.51/0.97  fof(f31,plain,(
% 3.51/0.97    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/0.97    inference(flattening,[],[f30])).
% 3.51/0.97  
% 3.51/0.97  fof(f42,plain,(
% 3.51/0.97    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/0.97    inference(nnf_transformation,[],[f31])).
% 3.51/0.97  
% 3.51/0.97  fof(f43,plain,(
% 3.51/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/0.97    inference(flattening,[],[f42])).
% 3.51/0.97  
% 3.51/0.97  fof(f44,plain,(
% 3.51/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/0.97    inference(rectify,[],[f43])).
% 3.51/0.97  
% 3.51/0.97  fof(f48,plain,(
% 3.51/0.97    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK5(X4),X1) & m1_connsp_2(sK5(X4),X0,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.51/0.97    introduced(choice_axiom,[])).
% 3.51/0.97  
% 3.51/0.97  fof(f47,plain,(
% 3.51/0.97    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.51/0.97    introduced(choice_axiom,[])).
% 3.51/0.97  
% 3.51/0.97  fof(f46,plain,(
% 3.51/0.97    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK3,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK3) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.51/0.97    introduced(choice_axiom,[])).
% 3.51/0.97  
% 3.51/0.97  fof(f45,plain,(
% 3.51/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK2,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.51/0.97    introduced(choice_axiom,[])).
% 3.51/0.97  
% 3.51/0.97  fof(f49,plain,(
% 3.51/0.97    (((! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) & (! [X4] : ((r1_tarski(sK5(X4),sK3) & m1_connsp_2(sK5(X4),sK2,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.51/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f44,f48,f47,f46,f45])).
% 3.51/0.97  
% 3.51/0.97  fof(f74,plain,(
% 3.51/0.97    l1_pre_topc(sK2)),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f5,axiom,(
% 3.51/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f17,plain,(
% 3.51/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.51/0.97    inference(ennf_transformation,[],[f5])).
% 3.51/0.97  
% 3.51/0.97  fof(f18,plain,(
% 3.51/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.51/0.97    inference(flattening,[],[f17])).
% 3.51/0.97  
% 3.51/0.97  fof(f59,plain,(
% 3.51/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f18])).
% 3.51/0.97  
% 3.51/0.97  fof(f81,plain,(
% 3.51/0.97    ( ! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f10,axiom,(
% 3.51/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f26,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.97    inference(ennf_transformation,[],[f10])).
% 3.51/0.97  
% 3.51/0.97  fof(f27,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.97    inference(flattening,[],[f26])).
% 3.51/0.97  
% 3.51/0.97  fof(f41,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.97    inference(nnf_transformation,[],[f27])).
% 3.51/0.97  
% 3.51/0.97  fof(f70,plain,(
% 3.51/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f41])).
% 3.51/0.97  
% 3.51/0.97  fof(f72,plain,(
% 3.51/0.97    ~v2_struct_0(sK2)),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f73,plain,(
% 3.51/0.97    v2_pre_topc(sK2)),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f79,plain,(
% 3.51/0.97    m1_subset_1(sK4,u1_struct_0(sK2)) | ~v3_pre_topc(sK3,sK2)),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f75,plain,(
% 3.51/0.97    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f80,plain,(
% 3.51/0.97    r2_hidden(sK4,sK3) | ~v3_pre_topc(sK3,sK2)),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f1,axiom,(
% 3.51/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f32,plain,(
% 3.51/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.51/0.97    inference(nnf_transformation,[],[f1])).
% 3.51/0.97  
% 3.51/0.97  fof(f33,plain,(
% 3.51/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.51/0.97    inference(flattening,[],[f32])).
% 3.51/0.97  
% 3.51/0.97  fof(f50,plain,(
% 3.51/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.51/0.97    inference(cnf_transformation,[],[f33])).
% 3.51/0.97  
% 3.51/0.97  fof(f83,plain,(
% 3.51/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.51/0.97    inference(equality_resolution,[],[f50])).
% 3.51/0.97  
% 3.51/0.97  fof(f11,axiom,(
% 3.51/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f28,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.97    inference(ennf_transformation,[],[f11])).
% 3.51/0.97  
% 3.51/0.97  fof(f29,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.97    inference(flattening,[],[f28])).
% 3.51/0.97  
% 3.51/0.97  fof(f71,plain,(
% 3.51/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f29])).
% 3.51/0.97  
% 3.51/0.97  fof(f3,axiom,(
% 3.51/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f15,plain,(
% 3.51/0.97    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.97    inference(ennf_transformation,[],[f3])).
% 3.51/0.97  
% 3.51/0.97  fof(f16,plain,(
% 3.51/0.97    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.97    inference(flattening,[],[f15])).
% 3.51/0.97  
% 3.51/0.97  fof(f34,plain,(
% 3.51/0.97    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.51/0.97    introduced(choice_axiom,[])).
% 3.51/0.97  
% 3.51/0.97  fof(f35,plain,(
% 3.51/0.97    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f34])).
% 3.51/0.97  
% 3.51/0.97  fof(f56,plain,(
% 3.51/0.97    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.97    inference(cnf_transformation,[],[f35])).
% 3.51/0.97  
% 3.51/0.97  fof(f77,plain,(
% 3.51/0.97    ( ! [X4] : (m1_connsp_2(sK5(X4),sK2,X4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f69,plain,(
% 3.51/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f41])).
% 3.51/0.97  
% 3.51/0.97  fof(f76,plain,(
% 3.51/0.97    ( ! [X4] : (m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f78,plain,(
% 3.51/0.97    ( ! [X4] : (r1_tarski(sK5(X4),sK3) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f49])).
% 3.51/0.97  
% 3.51/0.97  fof(f9,axiom,(
% 3.51/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f24,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.51/0.97    inference(ennf_transformation,[],[f9])).
% 3.51/0.97  
% 3.51/0.97  fof(f25,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.51/0.97    inference(flattening,[],[f24])).
% 3.51/0.97  
% 3.51/0.97  fof(f67,plain,(
% 3.51/0.97    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f25])).
% 3.51/0.97  
% 3.51/0.97  fof(f68,plain,(
% 3.51/0.97    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f25])).
% 3.51/0.97  
% 3.51/0.97  fof(f55,plain,(
% 3.51/0.97    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.97    inference(cnf_transformation,[],[f35])).
% 3.51/0.97  
% 3.51/0.97  fof(f52,plain,(
% 3.51/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f33])).
% 3.51/0.97  
% 3.51/0.97  fof(f6,axiom,(
% 3.51/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.51/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.97  
% 3.51/0.97  fof(f19,plain,(
% 3.51/0.97    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.97    inference(ennf_transformation,[],[f6])).
% 3.51/0.97  
% 3.51/0.97  fof(f60,plain,(
% 3.51/0.97    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.97    inference(cnf_transformation,[],[f19])).
% 3.51/0.97  
% 3.51/0.97  cnf(c_3,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.97      | ~ r2_hidden(X2,X0)
% 3.51/0.97      | r2_hidden(X2,X1) ),
% 3.51/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_7,plain,
% 3.51/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.51/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_239,plain,
% 3.51/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.51/0.97      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_240,plain,
% 3.51/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.51/0.97      inference(renaming,[status(thm)],[c_239]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_303,plain,
% 3.51/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.51/0.97      inference(bin_hyper_res,[status(thm)],[c_3,c_240]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_4552,plain,
% 3.51/0.97      ( r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),X0)
% 3.51/0.97      | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))))
% 3.51/0.97      | ~ r1_tarski(k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))),X0) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_303]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_13353,plain,
% 3.51/0.97      ( ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))))
% 3.51/0.97      | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
% 3.51/0.97      | ~ r1_tarski(k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,sK3)) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_4552]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_11,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ r1_tarski(X0,X2)
% 3.51/0.97      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.51/0.97      | ~ l1_pre_topc(X1) ),
% 3.51/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_29,negated_conjecture,
% 3.51/0.97      ( l1_pre_topc(sK2) ),
% 3.51/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_724,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ r1_tarski(X0,X2)
% 3.51/0.97      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.51/0.97      | sK2 != X1 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_725,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r1_tarski(X0,X1)
% 3.51/0.97      | r1_tarski(k1_tops_1(sK2,X0),k1_tops_1(sK2,X1)) ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_724]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_4394,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | r1_tarski(k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,X0))
% 3.51/0.97      | ~ r1_tarski(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),X0) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_725]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_7390,plain,
% 3.51/0.97      ( ~ m1_subset_1(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | r1_tarski(k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,sK3))
% 3.51/0.97      | ~ r1_tarski(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_4394]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_9,plain,
% 3.51/0.97      ( m1_subset_1(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.51/0.97      | ~ r2_hidden(X0,X2) ),
% 3.51/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2940,plain,
% 3.51/0.97      ( m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),X0)
% 3.51/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.51/0.97      | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_4319,plain,
% 3.51/0.97      ( m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_2940]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_22,negated_conjecture,
% 3.51/0.97      ( ~ m1_connsp_2(X0,sK2,sK4)
% 3.51/0.97      | ~ v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r1_tarski(X0,sK3) ),
% 3.51/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_19,plain,
% 3.51/0.97      ( m1_connsp_2(X0,X1,X2)
% 3.51/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.51/0.97      | v2_struct_0(X1)
% 3.51/0.97      | ~ v2_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X1) ),
% 3.51/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_31,negated_conjecture,
% 3.51/0.97      ( ~ v2_struct_0(sK2) ),
% 3.51/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_468,plain,
% 3.51/0.97      ( m1_connsp_2(X0,X1,X2)
% 3.51/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.51/0.97      | ~ v2_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | sK2 != X1 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_469,plain,
% 3.51/0.97      ( m1_connsp_2(X0,sK2,X1)
% 3.51/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.51/0.97      | ~ v2_pre_topc(sK2)
% 3.51/0.97      | ~ l1_pre_topc(sK2) ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_468]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_30,negated_conjecture,
% 3.51/0.97      ( v2_pre_topc(sK2) ),
% 3.51/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_473,plain,
% 3.51/0.97      ( m1_connsp_2(X0,sK2,X1)
% 3.51/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_469,c_30,c_29]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_815,plain,
% 3.51/0.97      ( ~ v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(X0,k1_tops_1(sK2,X2))
% 3.51/0.97      | ~ r1_tarski(X1,sK3)
% 3.51/0.97      | X2 != X1
% 3.51/0.97      | sK4 != X0
% 3.51/0.97      | sK2 != sK2 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_22,c_473]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_816,plain,
% 3.51/0.97      ( ~ v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.51/0.97      | ~ r2_hidden(sK4,k1_tops_1(sK2,X0))
% 3.51/0.97      | ~ r1_tarski(X0,sK3) ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_815]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_24,negated_conjecture,
% 3.51/0.97      ( ~ v3_pre_topc(sK3,sK2) | m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.51/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_820,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ r2_hidden(sK4,k1_tops_1(sK2,X0))
% 3.51/0.97      | ~ r1_tarski(X0,sK3) ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_816,c_24]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_821,plain,
% 3.51/0.97      ( ~ v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(sK4,k1_tops_1(sK2,X0))
% 3.51/0.97      | ~ r1_tarski(X0,sK3) ),
% 3.51/0.97      inference(renaming,[status(thm)],[c_820]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1795,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2) != iProver_top
% 3.51/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/0.97      | r2_hidden(sK4,k1_tops_1(sK2,X0)) != iProver_top
% 3.51/0.97      | r1_tarski(X0,sK3) != iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_28,negated_conjecture,
% 3.51/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.51/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_35,plain,
% 3.51/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_23,negated_conjecture,
% 3.51/0.97      ( ~ v3_pre_topc(sK3,sK2) | r2_hidden(sK4,sK3) ),
% 3.51/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_46,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2) != iProver_top
% 3.51/0.97      | r2_hidden(sK4,sK3) = iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2,plain,
% 3.51/0.97      ( r1_tarski(X0,X0) ),
% 3.51/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2175,plain,
% 3.51/0.97      ( r1_tarski(sK3,sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2178,plain,
% 3.51/0.97      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_2175]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_21,plain,
% 3.51/0.97      ( m1_connsp_2(X0,X1,X2)
% 3.51/0.97      | ~ v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ r2_hidden(X2,X0)
% 3.51/0.97      | v2_struct_0(X1)
% 3.51/0.97      | ~ v2_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X1) ),
% 3.51/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_415,plain,
% 3.51/0.97      ( m1_connsp_2(X0,X1,X2)
% 3.51/0.97      | ~ v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ r2_hidden(X2,X0)
% 3.51/0.97      | ~ v2_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | sK2 != X1 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_416,plain,
% 3.51/0.97      ( m1_connsp_2(X0,sK2,X1)
% 3.51/0.97      | ~ v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(X1,X0)
% 3.51/0.97      | ~ v2_pre_topc(sK2)
% 3.51/0.97      | ~ l1_pre_topc(sK2) ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_415]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_420,plain,
% 3.51/0.97      ( m1_connsp_2(X0,sK2,X1)
% 3.51/0.97      | ~ v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(X1,X0) ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_416,c_30,c_29]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_436,plain,
% 3.51/0.97      ( m1_connsp_2(X0,sK2,X1)
% 3.51/0.97      | ~ v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(X1,X0) ),
% 3.51/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_420,c_9]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_839,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(X2,X0)
% 3.51/0.97      | ~ r1_tarski(X1,sK3)
% 3.51/0.97      | X0 != X1
% 3.51/0.97      | sK4 != X2
% 3.51/0.97      | sK2 != sK2 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_22,c_436]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_840,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(sK4,X0)
% 3.51/0.97      | ~ r1_tarski(X0,sK3) ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_839]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2849,plain,
% 3.51/0.97      ( ~ v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(sK4,sK3)
% 3.51/0.97      | ~ r1_tarski(sK3,sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_840]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2850,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2) != iProver_top
% 3.51/0.97      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/0.97      | r2_hidden(sK4,sK3) != iProver_top
% 3.51/0.97      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_2849]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_3275,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2) != iProver_top ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_1795,c_35,c_46,c_2178,c_2850]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_4,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.51/0.97      | ~ r2_hidden(sK0(X1,X0,X2),X2)
% 3.51/0.97      | r1_tarski(X0,X2) ),
% 3.51/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_304,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.97      | ~ r2_hidden(sK0(X1,X2,X0),X0)
% 3.51/0.97      | ~ r1_tarski(X2,X1)
% 3.51/0.97      | r1_tarski(X2,X0) ),
% 3.51/0.97      inference(bin_hyper_res,[status(thm)],[c_4,c_240]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_993,plain,
% 3.51/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.51/0.97      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_994,plain,
% 3.51/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.51/0.97      inference(renaming,[status(thm)],[c_993]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1046,plain,
% 3.51/0.97      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.51/0.97      | ~ r1_tarski(X2,X0)
% 3.51/0.97      | ~ r1_tarski(X1,X0)
% 3.51/0.97      | r1_tarski(X1,X2) ),
% 3.51/0.97      inference(bin_hyper_res,[status(thm)],[c_304,c_994]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2182,plain,
% 3.51/0.97      ( ~ r2_hidden(sK0(X0,sK3,X1),X1)
% 3.51/0.97      | ~ r1_tarski(X1,X0)
% 3.51/0.97      | ~ r1_tarski(sK3,X0)
% 3.51/0.97      | r1_tarski(sK3,X1) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_1046]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2384,plain,
% 3.51/0.97      ( ~ r2_hidden(sK0(sK3,sK3,X0),X0)
% 3.51/0.97      | ~ r1_tarski(X0,sK3)
% 3.51/0.97      | r1_tarski(sK3,X0)
% 3.51/0.97      | ~ r1_tarski(sK3,sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_2182]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_3270,plain,
% 3.51/0.97      ( ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
% 3.51/0.97      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 3.51/0.97      | r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 3.51/0.97      | ~ r1_tarski(sK3,sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_2384]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_26,negated_conjecture,
% 3.51/0.97      ( m1_connsp_2(sK5(X0),sK2,X0)
% 3.51/0.97      | v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.51/0.97      | ~ r2_hidden(X0,sK3) ),
% 3.51/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_20,plain,
% 3.51/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 3.51/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.51/0.97      | v2_struct_0(X1)
% 3.51/0.97      | ~ v2_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X1) ),
% 3.51/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_444,plain,
% 3.51/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 3.51/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.51/0.97      | ~ v2_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | sK2 != X1 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_445,plain,
% 3.51/0.97      ( ~ m1_connsp_2(X0,sK2,X1)
% 3.51/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.51/0.97      | ~ v2_pre_topc(sK2)
% 3.51/0.97      | ~ l1_pre_topc(sK2) ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_444]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_449,plain,
% 3.51/0.97      ( ~ m1_connsp_2(X0,sK2,X1)
% 3.51/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_445,c_30,c_29]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_860,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 3.51/0.97      | ~ r2_hidden(X0,sK3)
% 3.51/0.97      | X1 != X0
% 3.51/0.97      | sK5(X0) != X2
% 3.51/0.97      | sK2 != sK2 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_26,c_449]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_861,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.51/0.97      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 3.51/0.97      | ~ r2_hidden(X0,sK3) ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_860]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_27,negated_conjecture,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.51/0.97      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(X0,sK3) ),
% 3.51/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_865,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.51/0.97      | v3_pre_topc(sK3,sK2)
% 3.51/0.97      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 3.51/0.97      | ~ r2_hidden(X0,sK3) ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_861,c_27]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_866,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.51/0.97      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 3.51/0.97      | ~ r2_hidden(X0,sK3) ),
% 3.51/0.97      inference(renaming,[status(thm)],[c_865]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2945,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 3.51/0.97      | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3)))))
% 3.51/0.97      | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_866]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2946,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 3.51/0.97      | m1_subset_1(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_27]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_25,negated_conjecture,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.51/0.97      | ~ r2_hidden(X0,sK3)
% 3.51/0.97      | r1_tarski(sK5(X0),sK3) ),
% 3.51/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2947,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 3.51/0.97      | ~ r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3)
% 3.51/0.97      | r1_tarski(sK5(sK0(sK3,sK3,k1_tops_1(sK2,sK3))),sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_25]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1811,plain,
% 3.51/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_18,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ v2_pre_topc(X3)
% 3.51/0.97      | ~ l1_pre_topc(X3)
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | k1_tops_1(X1,X0) = X0 ),
% 3.51/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_646,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X3)
% 3.51/0.97      | k1_tops_1(X1,X0) = X0
% 3.51/0.97      | sK2 != X3 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_647,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(sK2)
% 3.51/0.97      | k1_tops_1(X1,X0) = X0 ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_646]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_651,plain,
% 3.51/0.97      ( ~ l1_pre_topc(X1)
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ v3_pre_topc(X0,X1)
% 3.51/0.97      | k1_tops_1(X1,X0) = X0 ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_647,c_29]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_652,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | k1_tops_1(X1,X0) = X0 ),
% 3.51/0.97      inference(renaming,[status(thm)],[c_651]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_706,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | k1_tops_1(X1,X0) = X0
% 3.51/0.97      | sK2 != X1 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_652,c_29]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_707,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | k1_tops_1(sK2,X0) = X0 ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_706]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1144,plain,
% 3.51/0.97      ( ~ v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | k1_tops_1(sK2,X0) = X0
% 3.51/0.97      | ~ sP2_iProver_split ),
% 3.51/0.97      inference(splitting,
% 3.51/0.97                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.51/0.97                [c_707]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1803,plain,
% 3.51/0.97      ( k1_tops_1(sK2,X0) = X0
% 3.51/0.97      | v3_pre_topc(X0,sK2) != iProver_top
% 3.51/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/0.97      | sP2_iProver_split != iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_1144]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1145,plain,
% 3.51/0.97      ( sP2_iProver_split | sP0_iProver_split ),
% 3.51/0.97      inference(splitting,
% 3.51/0.97                [splitting(split),new_symbols(definition,[])],
% 3.51/0.97                [c_707]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1181,plain,
% 3.51/0.97      ( sP2_iProver_split = iProver_top
% 3.51/0.97      | sP0_iProver_split = iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_1145]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1182,plain,
% 3.51/0.97      ( k1_tops_1(sK2,X0) = X0
% 3.51/0.97      | v3_pre_topc(X0,sK2) != iProver_top
% 3.51/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/0.97      | sP2_iProver_split != iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_1144]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_17,plain,
% 3.51/0.97      ( v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.51/0.97      | ~ v2_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X3)
% 3.51/0.97      | k1_tops_1(X1,X0) != X0 ),
% 3.51/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_528,plain,
% 3.51/0.97      ( v3_pre_topc(X0,X1)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.51/0.97      | ~ l1_pre_topc(X1)
% 3.51/0.97      | ~ l1_pre_topc(X3)
% 3.51/0.97      | k1_tops_1(X1,X0) != X0
% 3.51/0.97      | sK2 != X1 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_529,plain,
% 3.51/0.97      ( v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ l1_pre_topc(X2)
% 3.51/0.97      | ~ l1_pre_topc(sK2)
% 3.51/0.97      | k1_tops_1(sK2,X0) != X0 ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_528]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_533,plain,
% 3.51/0.97      ( ~ l1_pre_topc(X2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.51/0.97      | v3_pre_topc(X0,sK2)
% 3.51/0.97      | k1_tops_1(sK2,X0) != X0 ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_529,c_29]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_534,plain,
% 3.51/0.97      ( v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ l1_pre_topc(X2)
% 3.51/0.97      | k1_tops_1(sK2,X0) != X0 ),
% 3.51/0.97      inference(renaming,[status(thm)],[c_533]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_754,plain,
% 3.51/0.97      ( v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | k1_tops_1(sK2,X0) != X0
% 3.51/0.97      | sK2 != X2 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_29,c_534]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_755,plain,
% 3.51/0.97      ( v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | k1_tops_1(sK2,X0) != X0 ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_754]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1141,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | ~ sP0_iProver_split ),
% 3.51/0.97      inference(splitting,
% 3.51/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.51/0.97                [c_755]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1799,plain,
% 3.51/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/0.97      | sP0_iProver_split != iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_1141]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2131,plain,
% 3.51/0.97      ( sP0_iProver_split != iProver_top ),
% 3.51/0.97      inference(superposition,[status(thm)],[c_1811,c_1799]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2779,plain,
% 3.51/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/0.97      | v3_pre_topc(X0,sK2) != iProver_top
% 3.51/0.97      | k1_tops_1(sK2,X0) = X0 ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_1803,c_1181,c_1182,c_2131]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2780,plain,
% 3.51/0.97      ( k1_tops_1(sK2,X0) = X0
% 3.51/0.97      | v3_pre_topc(X0,sK2) != iProver_top
% 3.51/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.51/0.97      inference(renaming,[status(thm)],[c_2779]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2789,plain,
% 3.51/0.97      ( k1_tops_1(sK2,sK3) = sK3 | v3_pre_topc(sK3,sK2) != iProver_top ),
% 3.51/0.97      inference(superposition,[status(thm)],[c_1811,c_2780]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2827,plain,
% 3.51/0.97      ( ~ v3_pre_topc(sK3,sK2) | k1_tops_1(sK2,sK3) = sK3 ),
% 3.51/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2789]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_5,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.51/0.97      | r2_hidden(sK0(X1,X0,X2),X0)
% 3.51/0.97      | r1_tarski(X0,X2) ),
% 3.51/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_305,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.97      | r2_hidden(sK0(X1,X2,X0),X2)
% 3.51/0.97      | ~ r1_tarski(X2,X1)
% 3.51/0.97      | r1_tarski(X2,X0) ),
% 3.51/0.97      inference(bin_hyper_res,[status(thm)],[c_5,c_240]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1047,plain,
% 3.51/0.97      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.51/0.97      | ~ r1_tarski(X2,X0)
% 3.51/0.97      | ~ r1_tarski(X1,X0)
% 3.51/0.97      | r1_tarski(X1,X2) ),
% 3.51/0.97      inference(bin_hyper_res,[status(thm)],[c_305,c_994]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2181,plain,
% 3.51/0.97      ( r2_hidden(sK0(X0,sK3,X1),sK3)
% 3.51/0.97      | ~ r1_tarski(X1,X0)
% 3.51/0.97      | ~ r1_tarski(sK3,X0)
% 3.51/0.97      | r1_tarski(sK3,X1) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_1047]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2299,plain,
% 3.51/0.97      ( r2_hidden(sK0(sK3,sK3,X0),sK3)
% 3.51/0.97      | ~ r1_tarski(X0,sK3)
% 3.51/0.97      | r1_tarski(sK3,X0)
% 3.51/0.97      | ~ r1_tarski(sK3,sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_2181]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2513,plain,
% 3.51/0.97      ( r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3)
% 3.51/0.97      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 3.51/0.97      | r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 3.51/0.97      | ~ r1_tarski(sK3,sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_2299]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_0,plain,
% 3.51/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.51/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2143,plain,
% 3.51/0.97      ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 3.51/0.97      | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 3.51/0.97      | k1_tops_1(sK2,sK3) = sK3 ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1142,plain,
% 3.51/0.97      ( v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | k1_tops_1(sK2,X0) != X0
% 3.51/0.97      | ~ sP1_iProver_split ),
% 3.51/0.97      inference(splitting,
% 3.51/0.97                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.51/0.97                [c_755]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1143,plain,
% 3.51/0.97      ( sP1_iProver_split | sP0_iProver_split ),
% 3.51/0.97      inference(splitting,
% 3.51/0.97                [splitting(split),new_symbols(definition,[])],
% 3.51/0.97                [c_755]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1248,plain,
% 3.51/0.97      ( k1_tops_1(sK2,X0) != X0
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | v3_pre_topc(X0,sK2) ),
% 3.51/0.97      inference(global_propositional_subsumption,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_1142,c_1143,c_1141]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_1249,plain,
% 3.51/0.97      ( v3_pre_topc(X0,sK2)
% 3.51/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | k1_tops_1(sK2,X0) != X0 ),
% 3.51/0.97      inference(renaming,[status(thm)],[c_1248]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2073,plain,
% 3.51/0.97      ( v3_pre_topc(sK3,sK2)
% 3.51/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | k1_tops_1(sK2,sK3) != sK3 ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_1249]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2074,plain,
% 3.51/0.97      ( k1_tops_1(sK2,sK3) != sK3
% 3.51/0.97      | v3_pre_topc(sK3,sK2) = iProver_top
% 3.51/0.97      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.51/0.97      inference(predicate_to_equality,[status(thm)],[c_2073]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_10,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.51/0.97      | ~ l1_pre_topc(X1) ),
% 3.51/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_742,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.51/0.97      | sK2 != X1 ),
% 3.51/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_743,plain,
% 3.51/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 3.51/0.97      inference(unflattening,[status(thm)],[c_742]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(c_2070,plain,
% 3.51/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/0.97      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 3.51/0.97      inference(instantiation,[status(thm)],[c_743]) ).
% 3.51/0.97  
% 3.51/0.97  cnf(contradiction,plain,
% 3.51/0.97      ( $false ),
% 3.51/0.97      inference(minisat,
% 3.51/0.97                [status(thm)],
% 3.51/0.97                [c_13353,c_7390,c_4319,c_3275,c_3270,c_2945,c_2946,
% 3.51/0.97                 c_2947,c_2827,c_2513,c_2175,c_2143,c_2074,c_2070,c_35,
% 3.51/0.97                 c_28]) ).
% 3.51/0.97  
% 3.51/0.97  
% 3.51/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/0.97  
% 3.51/0.97  ------                               Statistics
% 3.51/0.97  
% 3.51/0.97  ------ General
% 3.51/0.97  
% 3.51/0.97  abstr_ref_over_cycles:                  0
% 3.51/0.97  abstr_ref_under_cycles:                 0
% 3.51/0.97  gc_basic_clause_elim:                   0
% 3.51/0.97  forced_gc_time:                         0
% 3.51/0.97  parsing_time:                           0.01
% 3.51/0.97  unif_index_cands_time:                  0.
% 3.51/0.97  unif_index_add_time:                    0.
% 3.51/0.97  orderings_time:                         0.
% 3.51/0.97  out_proof_time:                         0.01
% 3.51/0.97  total_time:                             0.372
% 3.51/0.97  num_of_symbols:                         51
% 3.51/0.97  num_of_terms:                           7983
% 3.51/0.97  
% 3.51/0.97  ------ Preprocessing
% 3.51/0.97  
% 3.51/0.97  num_of_splits:                          4
% 3.51/0.97  num_of_split_atoms:                     3
% 3.51/0.97  num_of_reused_defs:                     1
% 3.51/0.97  num_eq_ax_congr_red:                    21
% 3.51/0.97  num_of_sem_filtered_clauses:            4
% 3.51/0.97  num_of_subtypes:                        0
% 3.51/0.97  monotx_restored_types:                  0
% 3.51/0.97  sat_num_of_epr_types:                   0
% 3.51/0.97  sat_num_of_non_cyclic_types:            0
% 3.51/0.97  sat_guarded_non_collapsed_types:        0
% 3.51/0.97  num_pure_diseq_elim:                    0
% 3.51/0.97  simp_replaced_by:                       0
% 3.51/0.97  res_preprocessed:                       136
% 3.51/0.97  prep_upred:                             0
% 3.51/0.97  prep_unflattend:                        22
% 3.51/0.97  smt_new_axioms:                         0
% 3.51/0.97  pred_elim_cands:                        4
% 3.51/0.97  pred_elim:                              4
% 3.51/0.97  pred_elim_cl:                           4
% 3.51/0.97  pred_elim_cycles:                       6
% 3.51/0.97  merged_defs:                            8
% 3.51/0.97  merged_defs_ncl:                        0
% 3.51/0.97  bin_hyper_res:                          15
% 3.51/0.97  prep_cycles:                            4
% 3.51/0.97  pred_elim_time:                         0.011
% 3.51/0.97  splitting_time:                         0.
% 3.51/0.97  sem_filter_time:                        0.
% 3.51/0.97  monotx_time:                            0.001
% 3.51/0.97  subtype_inf_time:                       0.
% 3.51/0.97  
% 3.51/0.97  ------ Problem properties
% 3.51/0.97  
% 3.51/0.97  clauses:                                31
% 3.51/0.97  conjectures:                            5
% 3.51/0.97  epr:                                    6
% 3.51/0.97  horn:                                   24
% 3.51/0.97  ground:                                 5
% 3.51/0.97  unary:                                  2
% 3.51/0.97  binary:                                 9
% 3.51/0.97  lits:                                   96
% 3.51/0.97  lits_eq:                                3
% 3.51/0.97  fd_pure:                                0
% 3.51/0.97  fd_pseudo:                              0
% 3.51/0.97  fd_cond:                                0
% 3.51/0.97  fd_pseudo_cond:                         1
% 3.51/0.97  ac_symbols:                             0
% 3.51/0.97  
% 3.51/0.97  ------ Propositional Solver
% 3.51/0.97  
% 3.51/0.97  prop_solver_calls:                      31
% 3.51/0.97  prop_fast_solver_calls:                 1712
% 3.51/0.97  smt_solver_calls:                       0
% 3.51/0.97  smt_fast_solver_calls:                  0
% 3.51/0.97  prop_num_of_clauses:                    4367
% 3.51/0.97  prop_preprocess_simplified:             9405
% 3.51/0.97  prop_fo_subsumed:                       69
% 3.51/0.97  prop_solver_time:                       0.
% 3.51/0.97  smt_solver_time:                        0.
% 3.51/0.97  smt_fast_solver_time:                   0.
% 3.51/0.97  prop_fast_solver_time:                  0.
% 3.51/0.97  prop_unsat_core_time:                   0.
% 3.51/0.97  
% 3.51/0.97  ------ QBF
% 3.51/0.97  
% 3.51/0.97  qbf_q_res:                              0
% 3.51/0.97  qbf_num_tautologies:                    0
% 3.51/0.97  qbf_prep_cycles:                        0
% 3.51/0.97  
% 3.51/0.97  ------ BMC1
% 3.51/0.97  
% 3.51/0.97  bmc1_current_bound:                     -1
% 3.51/0.97  bmc1_last_solved_bound:                 -1
% 3.51/0.97  bmc1_unsat_core_size:                   -1
% 3.51/0.97  bmc1_unsat_core_parents_size:           -1
% 3.51/0.97  bmc1_merge_next_fun:                    0
% 3.51/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.51/0.97  
% 3.51/0.97  ------ Instantiation
% 3.51/0.97  
% 3.51/0.97  inst_num_of_clauses:                    1261
% 3.51/0.97  inst_num_in_passive:                    618
% 3.51/0.97  inst_num_in_active:                     638
% 3.51/0.97  inst_num_in_unprocessed:                5
% 3.51/0.97  inst_num_of_loops:                      708
% 3.51/0.97  inst_num_of_learning_restarts:          0
% 3.51/0.97  inst_num_moves_active_passive:          63
% 3.51/0.97  inst_lit_activity:                      0
% 3.51/0.97  inst_lit_activity_moves:                0
% 3.51/0.97  inst_num_tautologies:                   0
% 3.51/0.97  inst_num_prop_implied:                  0
% 3.51/0.97  inst_num_existing_simplified:           0
% 3.51/0.97  inst_num_eq_res_simplified:             0
% 3.51/0.97  inst_num_child_elim:                    0
% 3.51/0.97  inst_num_of_dismatching_blockings:      488
% 3.51/0.97  inst_num_of_non_proper_insts:           1970
% 3.51/0.97  inst_num_of_duplicates:                 0
% 3.51/0.97  inst_inst_num_from_inst_to_res:         0
% 3.51/0.97  inst_dismatching_checking_time:         0.
% 3.51/0.97  
% 3.51/0.97  ------ Resolution
% 3.51/0.97  
% 3.51/0.97  res_num_of_clauses:                     0
% 3.51/0.97  res_num_in_passive:                     0
% 3.51/0.97  res_num_in_active:                      0
% 3.51/0.97  res_num_of_loops:                       140
% 3.51/0.97  res_forward_subset_subsumed:            232
% 3.51/0.97  res_backward_subset_subsumed:           4
% 3.51/0.97  res_forward_subsumed:                   0
% 3.51/0.97  res_backward_subsumed:                  0
% 3.51/0.97  res_forward_subsumption_resolution:     2
% 3.51/0.97  res_backward_subsumption_resolution:    0
% 3.51/0.97  res_clause_to_clause_subsumption:       1910
% 3.51/0.97  res_orphan_elimination:                 0
% 3.51/0.97  res_tautology_del:                      225
% 3.51/0.97  res_num_eq_res_simplified:              0
% 3.51/0.97  res_num_sel_changes:                    0
% 3.51/0.97  res_moves_from_active_to_pass:          0
% 3.51/0.97  
% 3.51/0.97  ------ Superposition
% 3.51/0.97  
% 3.51/0.97  sup_time_total:                         0.
% 3.51/0.97  sup_time_generating:                    0.
% 3.51/0.97  sup_time_sim_full:                      0.
% 3.51/0.97  sup_time_sim_immed:                     0.
% 3.51/0.97  
% 3.51/0.97  sup_num_of_clauses:                     242
% 3.51/0.97  sup_num_in_active:                      137
% 3.51/0.97  sup_num_in_passive:                     105
% 3.51/0.97  sup_num_of_loops:                       140
% 3.51/0.97  sup_fw_superposition:                   240
% 3.51/0.97  sup_bw_superposition:                   111
% 3.51/0.97  sup_immediate_simplified:               66
% 3.51/0.97  sup_given_eliminated:                   1
% 3.51/0.97  comparisons_done:                       0
% 3.51/0.97  comparisons_avoided:                    0
% 3.51/0.97  
% 3.51/0.97  ------ Simplifications
% 3.51/0.97  
% 3.51/0.97  
% 3.51/0.97  sim_fw_subset_subsumed:                 26
% 3.51/0.97  sim_bw_subset_subsumed:                 6
% 3.51/0.97  sim_fw_subsumed:                        32
% 3.51/0.97  sim_bw_subsumed:                        9
% 3.51/0.97  sim_fw_subsumption_res:                 5
% 3.51/0.97  sim_bw_subsumption_res:                 0
% 3.51/0.97  sim_tautology_del:                      18
% 3.51/0.97  sim_eq_tautology_del:                   5
% 3.51/0.97  sim_eq_res_simp:                        0
% 3.51/0.97  sim_fw_demodulated:                     0
% 3.51/0.97  sim_bw_demodulated:                     0
% 3.51/0.97  sim_light_normalised:                   0
% 3.51/0.97  sim_joinable_taut:                      0
% 3.51/0.97  sim_joinable_simp:                      0
% 3.51/0.97  sim_ac_normalised:                      0
% 3.51/0.97  sim_smt_subsumption:                    0
% 3.51/0.97  
%------------------------------------------------------------------------------
