%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:24 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 797 expanded)
%              Number of clauses        :   98 ( 169 expanded)
%              Number of leaves         :   16 ( 232 expanded)
%              Depth                    :   23
%              Number of atoms          :  820 (8663 expanded)
%              Number of equality atoms :   90 ( 184 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f29])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(rectify,[],[f41])).

fof(f46,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK5(X4),X1)
        & m1_connsp_2(sK5(X4),X0,X4)
        & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f42,f46,f45,f44,f43])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ! [X4] :
      ( m1_connsp_2(sK5(X4),sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f25])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f67,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ! [X4] :
      ( r1_tarski(sK5(X4),sK3)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | ~ m1_connsp_2(X3,sK2,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

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

fof(f14,plain,(
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
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK1(X0,X1,X2),X2)
            & r2_hidden(sK1(X0,X1,X2),X1)
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3378,plain,
    ( r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),X0)
    | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))))
    | ~ r1_tarski(k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7628,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))))
    | r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
    | ~ r1_tarski(k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3378])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3)
    | r1_tarski(k1_tops_1(sK2,X0),k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_3203,plain,
    ( ~ m1_subset_1(sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,sK3))
    | ~ r1_tarski(sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_22,negated_conjecture,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_16,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_329,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_330,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_334,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_26,c_25])).

cnf(c_643,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r2_hidden(X0,sK3)
    | X1 != X0
    | sK5(X0) != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_334])).

cnf(c_644,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v3_pre_topc(sK3,sK2)
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_23])).

cnf(c_649,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_648])).

cnf(c_2936,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))))
    | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_2937,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | m1_subset_1(sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK5(X0),sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2938,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),sK3)
    | r1_tarski(sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1304,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK2,sK4)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_302,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_303,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_307,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_26,c_25])).

cnf(c_616,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | ~ r1_tarski(X2,sK3)
    | X0 != X2
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_307])).

cnf(c_617,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,X0)
    | ~ r1_tarski(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_20,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK3,sK2)
    | ~ v3_pre_topc(X0,sK2)
    | ~ r2_hidden(sK4,X0)
    | ~ r1_tarski(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_617,c_20])).

cnf(c_622,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,X0)
    | ~ r1_tarski(X0,sK3) ),
    inference(renaming,[status(thm)],[c_621])).

cnf(c_1291,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,X0) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_2367,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1304,c_1291])).

cnf(c_19,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_42,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1616,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1619,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1616])).

cnf(c_2762,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2367,c_42,c_1619])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X2,X0),X1)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1728,plain,
    ( m1_subset_1(sK1(X0,sK3,k1_tops_1(sK2,sK3)),X0)
    | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2690,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1730,plain,
    ( ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK1(X0,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2598,plain,
    ( ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1729,plain,
    ( ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r2_hidden(sK1(X0,sK3,k1_tops_1(sK2,sK3)),sK3)
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2595,plain,
    ( ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),sK3)
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_418,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_419,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_423,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_25])).

cnf(c_424,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_423])).

cnf(c_455,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(X1,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_424,c_25])).

cnf(c_456,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_847,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_456])).

cnf(c_1302,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_848,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_456])).

cnf(c_881,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_882,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_13,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_393,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_394,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_398,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_25])).

cnf(c_399,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_398])).

cnf(c_527,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_399])).

cnf(c_528,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_844,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_528])).

cnf(c_1296,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_844])).

cnf(c_1572,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1304,c_1296])).

cnf(c_2234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | k1_tops_1(sK2,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1302,c_881,c_882,c_1572])).

cnf(c_2235,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2234])).

cnf(c_2242,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1304,c_2235])).

cnf(c_2264,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2242])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1600,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_845,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_528])).

cnf(c_846,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_528])).

cnf(c_938,plain,
    ( k1_tops_1(sK2,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_845,c_846,c_844])).

cnf(c_939,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_938])).

cnf(c_1540,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_1541,plain,
    ( k1_tops_1(sK2,sK3) != sK3
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1540])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k1_tops_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_1526,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7628,c_3203,c_2936,c_2937,c_2938,c_2762,c_2690,c_2598,c_2595,c_2264,c_1600,c_1541,c_1529,c_1526,c_31,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.16/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.99  
% 3.16/0.99  ------  iProver source info
% 3.16/0.99  
% 3.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.99  git: non_committed_changes: false
% 3.16/0.99  git: last_make_outside_of_git: false
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/0.99  
% 3.16/0.99  ------ General Options
% 3.16/0.99  
% 3.16/0.99  --fof                                   false
% 3.16/0.99  --time_out_real                         305.
% 3.16/0.99  --time_out_virtual                      -1.
% 3.16/0.99  --symbol_type_check                     false
% 3.16/0.99  --clausify_out                          false
% 3.16/0.99  --sig_cnt_out                           false
% 3.16/0.99  --trig_cnt_out                          false
% 3.16/0.99  --trig_cnt_out_tolerance                1.
% 3.16/0.99  --trig_cnt_out_sk_spl                   false
% 3.16/0.99  --abstr_cl_out                          false
% 3.16/0.99  
% 3.16/0.99  ------ Global Options
% 3.16/0.99  
% 3.16/0.99  --schedule                              default
% 3.16/0.99  --add_important_lit                     false
% 3.16/0.99  --prop_solver_per_cl                    1000
% 3.16/0.99  --min_unsat_core                        false
% 3.16/0.99  --soft_assumptions                      false
% 3.16/0.99  --soft_lemma_size                       3
% 3.16/0.99  --prop_impl_unit_size                   0
% 3.16/0.99  --prop_impl_unit                        []
% 3.16/0.99  --share_sel_clauses                     true
% 3.16/0.99  --reset_solvers                         false
% 3.16/0.99  --bc_imp_inh                            [conj_cone]
% 3.16/0.99  --conj_cone_tolerance                   3.
% 3.16/0.99  --extra_neg_conj                        none
% 3.16/0.99  --large_theory_mode                     true
% 3.16/0.99  --prolific_symb_bound                   200
% 3.16/0.99  --lt_threshold                          2000
% 3.16/0.99  --clause_weak_htbl                      true
% 3.16/0.99  --gc_record_bc_elim                     false
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing Options
% 3.16/0.99  
% 3.16/0.99  --preprocessing_flag                    true
% 3.16/0.99  --time_out_prep_mult                    0.1
% 3.16/0.99  --splitting_mode                        input
% 3.16/0.99  --splitting_grd                         true
% 3.16/0.99  --splitting_cvd                         false
% 3.16/0.99  --splitting_cvd_svl                     false
% 3.16/0.99  --splitting_nvd                         32
% 3.16/0.99  --sub_typing                            true
% 3.16/0.99  --prep_gs_sim                           true
% 3.16/0.99  --prep_unflatten                        true
% 3.16/0.99  --prep_res_sim                          true
% 3.16/0.99  --prep_upred                            true
% 3.16/0.99  --prep_sem_filter                       exhaustive
% 3.16/0.99  --prep_sem_filter_out                   false
% 3.16/0.99  --pred_elim                             true
% 3.16/0.99  --res_sim_input                         true
% 3.16/0.99  --eq_ax_congr_red                       true
% 3.16/0.99  --pure_diseq_elim                       true
% 3.16/0.99  --brand_transform                       false
% 3.16/0.99  --non_eq_to_eq                          false
% 3.16/0.99  --prep_def_merge                        true
% 3.16/0.99  --prep_def_merge_prop_impl              false
% 3.16/0.99  --prep_def_merge_mbd                    true
% 3.16/0.99  --prep_def_merge_tr_red                 false
% 3.16/0.99  --prep_def_merge_tr_cl                  false
% 3.16/0.99  --smt_preprocessing                     true
% 3.16/0.99  --smt_ac_axioms                         fast
% 3.16/0.99  --preprocessed_out                      false
% 3.16/0.99  --preprocessed_stats                    false
% 3.16/0.99  
% 3.16/0.99  ------ Abstraction refinement Options
% 3.16/0.99  
% 3.16/0.99  --abstr_ref                             []
% 3.16/0.99  --abstr_ref_prep                        false
% 3.16/0.99  --abstr_ref_until_sat                   false
% 3.16/0.99  --abstr_ref_sig_restrict                funpre
% 3.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.99  --abstr_ref_under                       []
% 3.16/0.99  
% 3.16/0.99  ------ SAT Options
% 3.16/0.99  
% 3.16/0.99  --sat_mode                              false
% 3.16/0.99  --sat_fm_restart_options                ""
% 3.16/0.99  --sat_gr_def                            false
% 3.16/0.99  --sat_epr_types                         true
% 3.16/0.99  --sat_non_cyclic_types                  false
% 3.16/0.99  --sat_finite_models                     false
% 3.16/0.99  --sat_fm_lemmas                         false
% 3.16/0.99  --sat_fm_prep                           false
% 3.16/0.99  --sat_fm_uc_incr                        true
% 3.16/0.99  --sat_out_model                         small
% 3.16/0.99  --sat_out_clauses                       false
% 3.16/0.99  
% 3.16/0.99  ------ QBF Options
% 3.16/0.99  
% 3.16/0.99  --qbf_mode                              false
% 3.16/0.99  --qbf_elim_univ                         false
% 3.16/0.99  --qbf_dom_inst                          none
% 3.16/0.99  --qbf_dom_pre_inst                      false
% 3.16/0.99  --qbf_sk_in                             false
% 3.16/0.99  --qbf_pred_elim                         true
% 3.16/0.99  --qbf_split                             512
% 3.16/0.99  
% 3.16/0.99  ------ BMC1 Options
% 3.16/0.99  
% 3.16/0.99  --bmc1_incremental                      false
% 3.16/0.99  --bmc1_axioms                           reachable_all
% 3.16/0.99  --bmc1_min_bound                        0
% 3.16/0.99  --bmc1_max_bound                        -1
% 3.16/0.99  --bmc1_max_bound_default                -1
% 3.16/0.99  --bmc1_symbol_reachability              true
% 3.16/0.99  --bmc1_property_lemmas                  false
% 3.16/0.99  --bmc1_k_induction                      false
% 3.16/0.99  --bmc1_non_equiv_states                 false
% 3.16/0.99  --bmc1_deadlock                         false
% 3.16/0.99  --bmc1_ucm                              false
% 3.16/0.99  --bmc1_add_unsat_core                   none
% 3.16/0.99  --bmc1_unsat_core_children              false
% 3.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.99  --bmc1_out_stat                         full
% 3.16/0.99  --bmc1_ground_init                      false
% 3.16/0.99  --bmc1_pre_inst_next_state              false
% 3.16/0.99  --bmc1_pre_inst_state                   false
% 3.16/0.99  --bmc1_pre_inst_reach_state             false
% 3.16/0.99  --bmc1_out_unsat_core                   false
% 3.16/0.99  --bmc1_aig_witness_out                  false
% 3.16/0.99  --bmc1_verbose                          false
% 3.16/0.99  --bmc1_dump_clauses_tptp                false
% 3.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.99  --bmc1_dump_file                        -
% 3.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.99  --bmc1_ucm_extend_mode                  1
% 3.16/0.99  --bmc1_ucm_init_mode                    2
% 3.16/0.99  --bmc1_ucm_cone_mode                    none
% 3.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.99  --bmc1_ucm_relax_model                  4
% 3.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.99  --bmc1_ucm_layered_model                none
% 3.16/0.99  --bmc1_ucm_max_lemma_size               10
% 3.16/0.99  
% 3.16/0.99  ------ AIG Options
% 3.16/0.99  
% 3.16/0.99  --aig_mode                              false
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation Options
% 3.16/0.99  
% 3.16/0.99  --instantiation_flag                    true
% 3.16/0.99  --inst_sos_flag                         false
% 3.16/0.99  --inst_sos_phase                        true
% 3.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel_side                     num_symb
% 3.16/0.99  --inst_solver_per_active                1400
% 3.16/0.99  --inst_solver_calls_frac                1.
% 3.16/0.99  --inst_passive_queue_type               priority_queues
% 3.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.99  --inst_passive_queues_freq              [25;2]
% 3.16/0.99  --inst_dismatching                      true
% 3.16/0.99  --inst_eager_unprocessed_to_passive     true
% 3.16/0.99  --inst_prop_sim_given                   true
% 3.16/0.99  --inst_prop_sim_new                     false
% 3.16/0.99  --inst_subs_new                         false
% 3.16/0.99  --inst_eq_res_simp                      false
% 3.16/0.99  --inst_subs_given                       false
% 3.16/0.99  --inst_orphan_elimination               true
% 3.16/0.99  --inst_learning_loop_flag               true
% 3.16/0.99  --inst_learning_start                   3000
% 3.16/0.99  --inst_learning_factor                  2
% 3.16/0.99  --inst_start_prop_sim_after_learn       3
% 3.16/0.99  --inst_sel_renew                        solver
% 3.16/0.99  --inst_lit_activity_flag                true
% 3.16/0.99  --inst_restr_to_given                   false
% 3.16/0.99  --inst_activity_threshold               500
% 3.16/0.99  --inst_out_proof                        true
% 3.16/0.99  
% 3.16/0.99  ------ Resolution Options
% 3.16/0.99  
% 3.16/0.99  --resolution_flag                       true
% 3.16/0.99  --res_lit_sel                           adaptive
% 3.16/0.99  --res_lit_sel_side                      none
% 3.16/0.99  --res_ordering                          kbo
% 3.16/0.99  --res_to_prop_solver                    active
% 3.16/0.99  --res_prop_simpl_new                    false
% 3.16/0.99  --res_prop_simpl_given                  true
% 3.16/0.99  --res_passive_queue_type                priority_queues
% 3.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.99  --res_passive_queues_freq               [15;5]
% 3.16/0.99  --res_forward_subs                      full
% 3.16/0.99  --res_backward_subs                     full
% 3.16/0.99  --res_forward_subs_resolution           true
% 3.16/0.99  --res_backward_subs_resolution          true
% 3.16/0.99  --res_orphan_elimination                true
% 3.16/0.99  --res_time_limit                        2.
% 3.16/0.99  --res_out_proof                         true
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Options
% 3.16/0.99  
% 3.16/0.99  --superposition_flag                    true
% 3.16/0.99  --sup_passive_queue_type                priority_queues
% 3.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.99  --demod_completeness_check              fast
% 3.16/0.99  --demod_use_ground                      true
% 3.16/0.99  --sup_to_prop_solver                    passive
% 3.16/0.99  --sup_prop_simpl_new                    true
% 3.16/0.99  --sup_prop_simpl_given                  true
% 3.16/0.99  --sup_fun_splitting                     false
% 3.16/0.99  --sup_smt_interval                      50000
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Simplification Setup
% 3.16/0.99  
% 3.16/0.99  --sup_indices_passive                   []
% 3.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_full_bw                           [BwDemod]
% 3.16/0.99  --sup_immed_triv                        [TrivRules]
% 3.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_immed_bw_main                     []
% 3.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  
% 3.16/0.99  ------ Combination Options
% 3.16/0.99  
% 3.16/0.99  --comb_res_mult                         3
% 3.16/0.99  --comb_sup_mult                         2
% 3.16/0.99  --comb_inst_mult                        10
% 3.16/0.99  
% 3.16/0.99  ------ Debug Options
% 3.16/0.99  
% 3.16/0.99  --dbg_backtrace                         false
% 3.16/0.99  --dbg_dump_prop_clauses                 false
% 3.16/0.99  --dbg_dump_prop_clauses_file            -
% 3.16/0.99  --dbg_out_stat                          false
% 3.16/0.99  ------ Parsing...
% 3.16/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.99  ------ Proving...
% 3.16/0.99  ------ Problem Properties 
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  clauses                                 27
% 3.16/0.99  conjectures                             5
% 3.16/0.99  EPR                                     6
% 3.16/0.99  Horn                                    19
% 3.16/0.99  unary                                   2
% 3.16/0.99  binary                                  11
% 3.16/0.99  lits                                    80
% 3.16/0.99  lits eq                                 4
% 3.16/0.99  fd_pure                                 0
% 3.16/0.99  fd_pseudo                               0
% 3.16/0.99  fd_cond                                 0
% 3.16/0.99  fd_pseudo_cond                          1
% 3.16/0.99  AC symbols                              0
% 3.16/0.99  
% 3.16/0.99  ------ Schedule dynamic 5 is on 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  Current options:
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/0.99  
% 3.16/0.99  ------ General Options
% 3.16/0.99  
% 3.16/0.99  --fof                                   false
% 3.16/0.99  --time_out_real                         305.
% 3.16/0.99  --time_out_virtual                      -1.
% 3.16/0.99  --symbol_type_check                     false
% 3.16/0.99  --clausify_out                          false
% 3.16/0.99  --sig_cnt_out                           false
% 3.16/0.99  --trig_cnt_out                          false
% 3.16/0.99  --trig_cnt_out_tolerance                1.
% 3.16/0.99  --trig_cnt_out_sk_spl                   false
% 3.16/0.99  --abstr_cl_out                          false
% 3.16/0.99  
% 3.16/0.99  ------ Global Options
% 3.16/0.99  
% 3.16/0.99  --schedule                              default
% 3.16/0.99  --add_important_lit                     false
% 3.16/0.99  --prop_solver_per_cl                    1000
% 3.16/0.99  --min_unsat_core                        false
% 3.16/0.99  --soft_assumptions                      false
% 3.16/0.99  --soft_lemma_size                       3
% 3.16/0.99  --prop_impl_unit_size                   0
% 3.16/0.99  --prop_impl_unit                        []
% 3.16/0.99  --share_sel_clauses                     true
% 3.16/0.99  --reset_solvers                         false
% 3.16/0.99  --bc_imp_inh                            [conj_cone]
% 3.16/0.99  --conj_cone_tolerance                   3.
% 3.16/0.99  --extra_neg_conj                        none
% 3.16/0.99  --large_theory_mode                     true
% 3.16/0.99  --prolific_symb_bound                   200
% 3.16/0.99  --lt_threshold                          2000
% 3.16/0.99  --clause_weak_htbl                      true
% 3.16/0.99  --gc_record_bc_elim                     false
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing Options
% 3.16/0.99  
% 3.16/0.99  --preprocessing_flag                    true
% 3.16/0.99  --time_out_prep_mult                    0.1
% 3.16/0.99  --splitting_mode                        input
% 3.16/0.99  --splitting_grd                         true
% 3.16/0.99  --splitting_cvd                         false
% 3.16/0.99  --splitting_cvd_svl                     false
% 3.16/0.99  --splitting_nvd                         32
% 3.16/0.99  --sub_typing                            true
% 3.16/0.99  --prep_gs_sim                           true
% 3.16/0.99  --prep_unflatten                        true
% 3.16/0.99  --prep_res_sim                          true
% 3.16/0.99  --prep_upred                            true
% 3.16/0.99  --prep_sem_filter                       exhaustive
% 3.16/0.99  --prep_sem_filter_out                   false
% 3.16/0.99  --pred_elim                             true
% 3.16/0.99  --res_sim_input                         true
% 3.16/0.99  --eq_ax_congr_red                       true
% 3.16/0.99  --pure_diseq_elim                       true
% 3.16/0.99  --brand_transform                       false
% 3.16/0.99  --non_eq_to_eq                          false
% 3.16/0.99  --prep_def_merge                        true
% 3.16/0.99  --prep_def_merge_prop_impl              false
% 3.16/0.99  --prep_def_merge_mbd                    true
% 3.16/0.99  --prep_def_merge_tr_red                 false
% 3.16/0.99  --prep_def_merge_tr_cl                  false
% 3.16/0.99  --smt_preprocessing                     true
% 3.16/0.99  --smt_ac_axioms                         fast
% 3.16/0.99  --preprocessed_out                      false
% 3.16/0.99  --preprocessed_stats                    false
% 3.16/0.99  
% 3.16/0.99  ------ Abstraction refinement Options
% 3.16/0.99  
% 3.16/0.99  --abstr_ref                             []
% 3.16/0.99  --abstr_ref_prep                        false
% 3.16/0.99  --abstr_ref_until_sat                   false
% 3.16/0.99  --abstr_ref_sig_restrict                funpre
% 3.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.99  --abstr_ref_under                       []
% 3.16/0.99  
% 3.16/0.99  ------ SAT Options
% 3.16/0.99  
% 3.16/0.99  --sat_mode                              false
% 3.16/0.99  --sat_fm_restart_options                ""
% 3.16/0.99  --sat_gr_def                            false
% 3.16/0.99  --sat_epr_types                         true
% 3.16/0.99  --sat_non_cyclic_types                  false
% 3.16/0.99  --sat_finite_models                     false
% 3.16/0.99  --sat_fm_lemmas                         false
% 3.16/0.99  --sat_fm_prep                           false
% 3.16/0.99  --sat_fm_uc_incr                        true
% 3.16/0.99  --sat_out_model                         small
% 3.16/0.99  --sat_out_clauses                       false
% 3.16/0.99  
% 3.16/0.99  ------ QBF Options
% 3.16/0.99  
% 3.16/0.99  --qbf_mode                              false
% 3.16/0.99  --qbf_elim_univ                         false
% 3.16/0.99  --qbf_dom_inst                          none
% 3.16/0.99  --qbf_dom_pre_inst                      false
% 3.16/0.99  --qbf_sk_in                             false
% 3.16/0.99  --qbf_pred_elim                         true
% 3.16/0.99  --qbf_split                             512
% 3.16/0.99  
% 3.16/0.99  ------ BMC1 Options
% 3.16/0.99  
% 3.16/0.99  --bmc1_incremental                      false
% 3.16/0.99  --bmc1_axioms                           reachable_all
% 3.16/0.99  --bmc1_min_bound                        0
% 3.16/0.99  --bmc1_max_bound                        -1
% 3.16/0.99  --bmc1_max_bound_default                -1
% 3.16/0.99  --bmc1_symbol_reachability              true
% 3.16/0.99  --bmc1_property_lemmas                  false
% 3.16/0.99  --bmc1_k_induction                      false
% 3.16/0.99  --bmc1_non_equiv_states                 false
% 3.16/0.99  --bmc1_deadlock                         false
% 3.16/0.99  --bmc1_ucm                              false
% 3.16/0.99  --bmc1_add_unsat_core                   none
% 3.16/0.99  --bmc1_unsat_core_children              false
% 3.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.99  --bmc1_out_stat                         full
% 3.16/0.99  --bmc1_ground_init                      false
% 3.16/0.99  --bmc1_pre_inst_next_state              false
% 3.16/0.99  --bmc1_pre_inst_state                   false
% 3.16/0.99  --bmc1_pre_inst_reach_state             false
% 3.16/0.99  --bmc1_out_unsat_core                   false
% 3.16/0.99  --bmc1_aig_witness_out                  false
% 3.16/0.99  --bmc1_verbose                          false
% 3.16/0.99  --bmc1_dump_clauses_tptp                false
% 3.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.99  --bmc1_dump_file                        -
% 3.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.99  --bmc1_ucm_extend_mode                  1
% 3.16/0.99  --bmc1_ucm_init_mode                    2
% 3.16/0.99  --bmc1_ucm_cone_mode                    none
% 3.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.99  --bmc1_ucm_relax_model                  4
% 3.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.99  --bmc1_ucm_layered_model                none
% 3.16/0.99  --bmc1_ucm_max_lemma_size               10
% 3.16/0.99  
% 3.16/0.99  ------ AIG Options
% 3.16/0.99  
% 3.16/0.99  --aig_mode                              false
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation Options
% 3.16/0.99  
% 3.16/0.99  --instantiation_flag                    true
% 3.16/0.99  --inst_sos_flag                         false
% 3.16/0.99  --inst_sos_phase                        true
% 3.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel_side                     none
% 3.16/0.99  --inst_solver_per_active                1400
% 3.16/0.99  --inst_solver_calls_frac                1.
% 3.16/0.99  --inst_passive_queue_type               priority_queues
% 3.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.99  --inst_passive_queues_freq              [25;2]
% 3.16/0.99  --inst_dismatching                      true
% 3.16/0.99  --inst_eager_unprocessed_to_passive     true
% 3.16/0.99  --inst_prop_sim_given                   true
% 3.16/0.99  --inst_prop_sim_new                     false
% 3.16/0.99  --inst_subs_new                         false
% 3.16/0.99  --inst_eq_res_simp                      false
% 3.16/0.99  --inst_subs_given                       false
% 3.16/0.99  --inst_orphan_elimination               true
% 3.16/0.99  --inst_learning_loop_flag               true
% 3.16/0.99  --inst_learning_start                   3000
% 3.16/0.99  --inst_learning_factor                  2
% 3.16/0.99  --inst_start_prop_sim_after_learn       3
% 3.16/0.99  --inst_sel_renew                        solver
% 3.16/0.99  --inst_lit_activity_flag                true
% 3.16/0.99  --inst_restr_to_given                   false
% 3.16/0.99  --inst_activity_threshold               500
% 3.16/0.99  --inst_out_proof                        true
% 3.16/0.99  
% 3.16/0.99  ------ Resolution Options
% 3.16/0.99  
% 3.16/0.99  --resolution_flag                       false
% 3.16/0.99  --res_lit_sel                           adaptive
% 3.16/0.99  --res_lit_sel_side                      none
% 3.16/0.99  --res_ordering                          kbo
% 3.16/0.99  --res_to_prop_solver                    active
% 3.16/0.99  --res_prop_simpl_new                    false
% 3.16/0.99  --res_prop_simpl_given                  true
% 3.16/0.99  --res_passive_queue_type                priority_queues
% 3.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.99  --res_passive_queues_freq               [15;5]
% 3.16/0.99  --res_forward_subs                      full
% 3.16/0.99  --res_backward_subs                     full
% 3.16/0.99  --res_forward_subs_resolution           true
% 3.16/0.99  --res_backward_subs_resolution          true
% 3.16/0.99  --res_orphan_elimination                true
% 3.16/0.99  --res_time_limit                        2.
% 3.16/0.99  --res_out_proof                         true
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Options
% 3.16/0.99  
% 3.16/0.99  --superposition_flag                    true
% 3.16/0.99  --sup_passive_queue_type                priority_queues
% 3.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.99  --demod_completeness_check              fast
% 3.16/0.99  --demod_use_ground                      true
% 3.16/0.99  --sup_to_prop_solver                    passive
% 3.16/0.99  --sup_prop_simpl_new                    true
% 3.16/0.99  --sup_prop_simpl_given                  true
% 3.16/0.99  --sup_fun_splitting                     false
% 3.16/0.99  --sup_smt_interval                      50000
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Simplification Setup
% 3.16/0.99  
% 3.16/0.99  --sup_indices_passive                   []
% 3.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_full_bw                           [BwDemod]
% 3.16/0.99  --sup_immed_triv                        [TrivRules]
% 3.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_immed_bw_main                     []
% 3.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  
% 3.16/0.99  ------ Combination Options
% 3.16/0.99  
% 3.16/0.99  --comb_res_mult                         3
% 3.16/0.99  --comb_sup_mult                         2
% 3.16/0.99  --comb_inst_mult                        10
% 3.16/0.99  
% 3.16/0.99  ------ Debug Options
% 3.16/0.99  
% 3.16/0.99  --dbg_backtrace                         false
% 3.16/0.99  --dbg_dump_prop_clauses                 false
% 3.16/0.99  --dbg_dump_prop_clauses_file            -
% 3.16/0.99  --dbg_out_stat                          false
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  ------ Proving...
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  % SZS status Theorem for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  fof(f1,axiom,(
% 3.16/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f13,plain,(
% 3.16/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f1])).
% 3.16/0.99  
% 3.16/0.99  fof(f31,plain,(
% 3.16/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/0.99    inference(nnf_transformation,[],[f13])).
% 3.16/0.99  
% 3.16/0.99  fof(f32,plain,(
% 3.16/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/0.99    inference(rectify,[],[f31])).
% 3.16/0.99  
% 3.16/0.99  fof(f33,plain,(
% 3.16/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f34,plain,(
% 3.16/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.16/0.99  
% 3.16/0.99  fof(f48,plain,(
% 3.16/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f34])).
% 3.16/0.99  
% 3.16/0.99  fof(f7,axiom,(
% 3.16/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f21,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.16/0.99    inference(ennf_transformation,[],[f7])).
% 3.16/0.99  
% 3.16/0.99  fof(f22,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.16/0.99    inference(flattening,[],[f21])).
% 3.16/0.99  
% 3.16/0.99  fof(f60,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f22])).
% 3.16/0.99  
% 3.16/0.99  fof(f11,conjecture,(
% 3.16/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f12,negated_conjecture,(
% 3.16/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.16/0.99    inference(negated_conjecture,[],[f11])).
% 3.16/0.99  
% 3.16/0.99  fof(f29,plain,(
% 3.16/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f12])).
% 3.16/0.99  
% 3.16/0.99  fof(f30,plain,(
% 3.16/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.16/0.99    inference(flattening,[],[f29])).
% 3.16/0.99  
% 3.16/0.99  fof(f40,plain,(
% 3.16/0.99    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.16/0.99    inference(nnf_transformation,[],[f30])).
% 3.16/0.99  
% 3.16/0.99  fof(f41,plain,(
% 3.16/0.99    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.16/0.99    inference(flattening,[],[f40])).
% 3.16/0.99  
% 3.16/0.99  fof(f42,plain,(
% 3.16/0.99    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.16/0.99    inference(rectify,[],[f41])).
% 3.16/0.99  
% 3.16/0.99  fof(f46,plain,(
% 3.16/0.99    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK5(X4),X1) & m1_connsp_2(sK5(X4),X0,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f45,plain,(
% 3.16/0.99    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f44,plain,(
% 3.16/0.99    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK3,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK3) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f43,plain,(
% 3.16/0.99    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK2,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f47,plain,(
% 3.16/0.99    (((! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) & (! [X4] : ((r1_tarski(sK5(X4),sK3) & m1_connsp_2(sK5(X4),sK2,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f42,f46,f45,f44,f43])).
% 3.16/0.99  
% 3.16/0.99  fof(f68,plain,(
% 3.16/0.99    l1_pre_topc(sK2)),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f71,plain,(
% 3.16/0.99    ( ! [X4] : (m1_connsp_2(sK5(X4),sK2,X4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f9,axiom,(
% 3.16/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f25,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f9])).
% 3.16/0.99  
% 3.16/0.99  fof(f26,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.99    inference(flattening,[],[f25])).
% 3.16/0.99  
% 3.16/0.99  fof(f39,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.99    inference(nnf_transformation,[],[f26])).
% 3.16/0.99  
% 3.16/0.99  fof(f63,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f39])).
% 3.16/0.99  
% 3.16/0.99  fof(f66,plain,(
% 3.16/0.99    ~v2_struct_0(sK2)),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f67,plain,(
% 3.16/0.99    v2_pre_topc(sK2)),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f70,plain,(
% 3.16/0.99    ( ! [X4] : (m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f72,plain,(
% 3.16/0.99    ( ! [X4] : (r1_tarski(sK5(X4),sK3) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f69,plain,(
% 3.16/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f75,plain,(
% 3.16/0.99    ( ! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f10,axiom,(
% 3.16/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f27,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f10])).
% 3.16/0.99  
% 3.16/0.99  fof(f28,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.99    inference(flattening,[],[f27])).
% 3.16/0.99  
% 3.16/0.99  fof(f65,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f28])).
% 3.16/0.99  
% 3.16/0.99  fof(f73,plain,(
% 3.16/0.99    m1_subset_1(sK4,u1_struct_0(sK2)) | ~v3_pre_topc(sK3,sK2)),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f74,plain,(
% 3.16/0.99    r2_hidden(sK4,sK3) | ~v3_pre_topc(sK3,sK2)),
% 3.16/0.99    inference(cnf_transformation,[],[f47])).
% 3.16/0.99  
% 3.16/0.99  fof(f2,axiom,(
% 3.16/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f35,plain,(
% 3.16/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/0.99    inference(nnf_transformation,[],[f2])).
% 3.16/0.99  
% 3.16/0.99  fof(f36,plain,(
% 3.16/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/0.99    inference(flattening,[],[f35])).
% 3.16/0.99  
% 3.16/0.99  fof(f51,plain,(
% 3.16/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.16/0.99    inference(cnf_transformation,[],[f36])).
% 3.16/0.99  
% 3.16/0.99  fof(f77,plain,(
% 3.16/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.16/0.99    inference(equality_resolution,[],[f51])).
% 3.16/0.99  
% 3.16/0.99  fof(f3,axiom,(
% 3.16/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f14,plain,(
% 3.16/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f3])).
% 3.16/0.99  
% 3.16/0.99  fof(f15,plain,(
% 3.16/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.16/0.99    inference(flattening,[],[f14])).
% 3.16/0.99  
% 3.16/0.99  fof(f37,plain,(
% 3.16/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),X0)))),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f38,plain,(
% 3.16/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f37])).
% 3.16/0.99  
% 3.16/0.99  fof(f54,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.16/0.99    inference(cnf_transformation,[],[f38])).
% 3.16/0.99  
% 3.16/0.99  fof(f56,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.16/0.99    inference(cnf_transformation,[],[f38])).
% 3.16/0.99  
% 3.16/0.99  fof(f55,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.16/0.99    inference(cnf_transformation,[],[f38])).
% 3.16/0.99  
% 3.16/0.99  fof(f8,axiom,(
% 3.16/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f23,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f8])).
% 3.16/0.99  
% 3.16/0.99  fof(f24,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.99    inference(flattening,[],[f23])).
% 3.16/0.99  
% 3.16/0.99  fof(f61,plain,(
% 3.16/0.99    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f24])).
% 3.16/0.99  
% 3.16/0.99  fof(f62,plain,(
% 3.16/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f24])).
% 3.16/0.99  
% 3.16/0.99  fof(f53,plain,(
% 3.16/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f36])).
% 3.16/0.99  
% 3.16/0.99  fof(f6,axiom,(
% 3.16/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f20,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.16/0.99    inference(ennf_transformation,[],[f6])).
% 3.16/0.99  
% 3.16/0.99  fof(f59,plain,(
% 3.16/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f20])).
% 3.16/0.99  
% 3.16/0.99  fof(f4,axiom,(
% 3.16/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f16,plain,(
% 3.16/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f4])).
% 3.16/0.99  
% 3.16/0.99  fof(f17,plain,(
% 3.16/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.16/0.99    inference(flattening,[],[f16])).
% 3.16/0.99  
% 3.16/0.99  fof(f57,plain,(
% 3.16/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f17])).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2,plain,
% 3.16/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.16/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3378,plain,
% 3.16/0.99      ( r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),X0)
% 3.16/0.99      | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))))
% 3.16/0.99      | ~ r1_tarski(k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))),X0) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_7628,plain,
% 3.16/0.99      ( ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))))
% 3.16/0.99      | r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
% 3.16/0.99      | ~ r1_tarski(k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,sK3)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_3378]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_12,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ r1_tarski(X0,X2)
% 3.16/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.16/0.99      | ~ l1_pre_topc(X1) ),
% 3.16/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_25,negated_conjecture,
% 3.16/0.99      ( l1_pre_topc(sK2) ),
% 3.16/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_473,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ r1_tarski(X0,X2)
% 3.16/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.16/0.99      | sK2 != X1 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_474,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r1_tarski(X1,X0)
% 3.16/0.99      | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1543,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r1_tarski(X0,sK3)
% 3.16/0.99      | r1_tarski(k1_tops_1(sK2,X0),k1_tops_1(sK2,sK3)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_474]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3203,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r1_tarski(k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))),k1_tops_1(sK2,sK3))
% 3.16/0.99      | ~ r1_tarski(sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3))),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_1543]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_22,negated_conjecture,
% 3.16/0.99      ( m1_connsp_2(sK5(X0),sK2,X0)
% 3.16/0.99      | v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.16/0.99      | ~ r2_hidden(X0,sK3) ),
% 3.16/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_16,plain,
% 3.16/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.16/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.16/0.99      | v2_struct_0(X1)
% 3.16/0.99      | ~ v2_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(X1) ),
% 3.16/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_27,negated_conjecture,
% 3.16/0.99      ( ~ v2_struct_0(sK2) ),
% 3.16/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_329,plain,
% 3.16/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.16/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.16/0.99      | ~ v2_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(X1)
% 3.16/0.99      | sK2 != X1 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_330,plain,
% 3.16/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 3.16/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.16/0.99      | ~ v2_pre_topc(sK2)
% 3.16/0.99      | ~ l1_pre_topc(sK2) ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_329]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_26,negated_conjecture,
% 3.16/0.99      ( v2_pre_topc(sK2) ),
% 3.16/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_334,plain,
% 3.16/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 3.16/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_330,c_26,c_25]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_643,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 3.16/0.99      | ~ r2_hidden(X0,sK3)
% 3.16/0.99      | X1 != X0
% 3.16/0.99      | sK5(X0) != X2
% 3.16/0.99      | sK2 != sK2 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_334]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_644,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 3.16/0.99      | ~ r2_hidden(X0,sK3) ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_643]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_23,negated_conjecture,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.16/0.99      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r2_hidden(X0,sK3) ),
% 3.16/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_648,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.16/0.99      | v3_pre_topc(sK3,sK2)
% 3.16/0.99      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 3.16/0.99      | ~ r2_hidden(X0,sK3) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_644,c_23]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_649,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.16/0.99      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 3.16/0.99      | ~ r2_hidden(X0,sK3) ),
% 3.16/0.99      inference(renaming,[status(thm)],[c_648]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2936,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 3.16/0.99      | r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)))))
% 3.16/0.99      | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_649]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2937,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 3.16/0.99      | m1_subset_1(sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_21,negated_conjecture,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.16/0.99      | ~ r2_hidden(X0,sK3)
% 3.16/0.99      | r1_tarski(sK5(X0),sK3) ),
% 3.16/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2938,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 3.16/0.99      | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),sK3)
% 3.16/0.99      | r1_tarski(sK5(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3))),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_24,negated_conjecture,
% 3.16/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.16/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1304,plain,
% 3.16/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_18,negated_conjecture,
% 3.16/0.99      ( ~ m1_connsp_2(X0,sK2,sK4)
% 3.16/0.99      | ~ v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r1_tarski(X0,sK3) ),
% 3.16/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_17,plain,
% 3.16/0.99      ( m1_connsp_2(X0,X1,X2)
% 3.16/0.99      | ~ v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ r2_hidden(X2,X0)
% 3.16/0.99      | v2_struct_0(X1)
% 3.16/0.99      | ~ v2_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(X1) ),
% 3.16/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_302,plain,
% 3.16/0.99      ( m1_connsp_2(X0,X1,X2)
% 3.16/0.99      | ~ v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ r2_hidden(X2,X0)
% 3.16/0.99      | ~ v2_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(X1)
% 3.16/0.99      | sK2 != X1 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_303,plain,
% 3.16/0.99      ( m1_connsp_2(X0,sK2,X1)
% 3.16/0.99      | ~ v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r2_hidden(X1,X0)
% 3.16/0.99      | ~ v2_pre_topc(sK2)
% 3.16/0.99      | ~ l1_pre_topc(sK2) ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_302]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_307,plain,
% 3.16/0.99      ( m1_connsp_2(X0,sK2,X1)
% 3.16/0.99      | ~ v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r2_hidden(X1,X0) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_303,c_26,c_25]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_616,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r2_hidden(X1,X0)
% 3.16/0.99      | ~ r1_tarski(X2,sK3)
% 3.16/0.99      | X0 != X2
% 3.16/0.99      | sK4 != X1
% 3.16/0.99      | sK2 != sK2 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_307]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_617,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.16/0.99      | ~ r2_hidden(sK4,X0)
% 3.16/0.99      | ~ r1_tarski(X0,sK3) ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_616]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_20,negated_conjecture,
% 3.16/0.99      ( ~ v3_pre_topc(sK3,sK2) | m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_621,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ r2_hidden(sK4,X0)
% 3.16/0.99      | ~ r1_tarski(X0,sK3) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_617,c_20]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_622,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r2_hidden(sK4,X0)
% 3.16/0.99      | ~ r1_tarski(X0,sK3) ),
% 3.16/0.99      inference(renaming,[status(thm)],[c_621]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1291,plain,
% 3.16/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.16/0.99      | v3_pre_topc(sK3,sK2) != iProver_top
% 3.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.99      | r2_hidden(sK4,X0) != iProver_top
% 3.16/0.99      | r1_tarski(X0,sK3) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2367,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2) != iProver_top
% 3.16/0.99      | r2_hidden(sK4,sK3) != iProver_top
% 3.16/0.99      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_1304,c_1291]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_19,negated_conjecture,
% 3.16/0.99      ( ~ v3_pre_topc(sK3,sK2) | r2_hidden(sK4,sK3) ),
% 3.16/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_42,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2) != iProver_top
% 3.16/0.99      | r2_hidden(sK4,sK3) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_5,plain,
% 3.16/0.99      ( r1_tarski(X0,X0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1616,plain,
% 3.16/0.99      ( r1_tarski(sK3,sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1619,plain,
% 3.16/0.99      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1616]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2762,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2) != iProver_top ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_2367,c_42,c_1619]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_8,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.16/0.99      | m1_subset_1(sK1(X1,X2,X0),X1)
% 3.16/0.99      | r1_tarski(X2,X0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1728,plain,
% 3.16/0.99      ( m1_subset_1(sK1(X0,sK3,k1_tops_1(sK2,sK3)),X0)
% 3.16/0.99      | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(X0))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.16/0.99      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2690,plain,
% 3.16/0.99      ( m1_subset_1(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),u1_struct_0(sK2))
% 3.16/0.99      | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_1728]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_6,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.16/0.99      | ~ r2_hidden(sK1(X1,X2,X0),X0)
% 3.16/0.99      | r1_tarski(X2,X0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1730,plain,
% 3.16/0.99      ( ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(X0))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.16/0.99      | ~ r2_hidden(sK1(X0,sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
% 3.16/0.99      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2598,plain,
% 3.16/0.99      ( ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),k1_tops_1(sK2,sK3))
% 3.16/0.99      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_1730]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_7,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.16/0.99      | r2_hidden(sK1(X1,X2,X0),X2)
% 3.16/0.99      | r1_tarski(X2,X0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1729,plain,
% 3.16/0.99      ( ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(X0))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.16/0.99      | r2_hidden(sK1(X0,sK3,k1_tops_1(sK2,sK3)),sK3)
% 3.16/0.99      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2595,plain,
% 3.16/0.99      ( ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r2_hidden(sK1(u1_struct_0(sK2),sK3,k1_tops_1(sK2,sK3)),sK3)
% 3.16/0.99      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_1729]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_14,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ v2_pre_topc(X3)
% 3.16/0.99      | ~ l1_pre_topc(X3)
% 3.16/0.99      | ~ l1_pre_topc(X1)
% 3.16/0.99      | k1_tops_1(X1,X0) = X0 ),
% 3.16/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_418,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.16/0.99      | ~ l1_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(X3)
% 3.16/0.99      | k1_tops_1(X1,X0) = X0
% 3.16/0.99      | sK2 != X3 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_419,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ l1_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(sK2)
% 3.16/0.99      | k1_tops_1(X1,X0) = X0 ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_418]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_423,plain,
% 3.16/0.99      ( ~ l1_pre_topc(X1)
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ v3_pre_topc(X0,X1)
% 3.16/0.99      | k1_tops_1(X1,X0) = X0 ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_419,c_25]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_424,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ l1_pre_topc(X1)
% 3.16/0.99      | k1_tops_1(X1,X0) = X0 ),
% 3.16/0.99      inference(renaming,[status(thm)],[c_423]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_455,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | k1_tops_1(X1,X0) = X0
% 3.16/0.99      | sK2 != X1 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_424,c_25]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_456,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | k1_tops_1(sK2,X0) = X0 ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_847,plain,
% 3.16/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | k1_tops_1(sK2,X0) = X0
% 3.16/0.99      | ~ sP2_iProver_split ),
% 3.16/0.99      inference(splitting,
% 3.16/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.16/0.99                [c_456]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1302,plain,
% 3.16/0.99      ( k1_tops_1(sK2,X0) = X0
% 3.16/0.99      | v3_pre_topc(X0,sK2) != iProver_top
% 3.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.99      | sP2_iProver_split != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_848,plain,
% 3.16/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 3.16/0.99      inference(splitting,
% 3.16/0.99                [splitting(split),new_symbols(definition,[])],
% 3.16/0.99                [c_456]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_881,plain,
% 3.16/0.99      ( sP2_iProver_split = iProver_top
% 3.16/0.99      | sP0_iProver_split = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_882,plain,
% 3.16/0.99      ( k1_tops_1(sK2,X0) = X0
% 3.16/0.99      | v3_pre_topc(X0,sK2) != iProver_top
% 3.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.99      | sP2_iProver_split != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_13,plain,
% 3.16/0.99      ( v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.16/0.99      | ~ v2_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(X3)
% 3.16/0.99      | k1_tops_1(X1,X0) != X0 ),
% 3.16/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_393,plain,
% 3.16/0.99      ( v3_pre_topc(X0,X1)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.16/0.99      | ~ l1_pre_topc(X1)
% 3.16/0.99      | ~ l1_pre_topc(X3)
% 3.16/0.99      | k1_tops_1(X1,X0) != X0
% 3.16/0.99      | sK2 != X1 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_394,plain,
% 3.16/0.99      ( v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ l1_pre_topc(X2)
% 3.16/0.99      | ~ l1_pre_topc(sK2)
% 3.16/0.99      | k1_tops_1(sK2,X0) != X0 ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_393]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_398,plain,
% 3.16/0.99      ( ~ l1_pre_topc(X2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.16/0.99      | v3_pre_topc(X0,sK2)
% 3.16/0.99      | k1_tops_1(sK2,X0) != X0 ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_394,c_25]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_399,plain,
% 3.16/0.99      ( v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ l1_pre_topc(X2)
% 3.16/0.99      | k1_tops_1(sK2,X0) != X0 ),
% 3.16/0.99      inference(renaming,[status(thm)],[c_398]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_527,plain,
% 3.16/0.99      ( v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | k1_tops_1(sK2,X0) != X0
% 3.16/0.99      | sK2 != X2 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_399]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_528,plain,
% 3.16/0.99      ( v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | k1_tops_1(sK2,X0) != X0 ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_527]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_844,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ sP0_iProver_split ),
% 3.16/0.99      inference(splitting,
% 3.16/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.16/0.99                [c_528]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1296,plain,
% 3.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.99      | sP0_iProver_split != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_844]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1572,plain,
% 3.16/0.99      ( sP0_iProver_split != iProver_top ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_1304,c_1296]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2234,plain,
% 3.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.16/0.99      | v3_pre_topc(X0,sK2) != iProver_top
% 3.16/0.99      | k1_tops_1(sK2,X0) = X0 ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_1302,c_881,c_882,c_1572]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2235,plain,
% 3.16/0.99      ( k1_tops_1(sK2,X0) = X0
% 3.16/0.99      | v3_pre_topc(X0,sK2) != iProver_top
% 3.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.16/0.99      inference(renaming,[status(thm)],[c_2234]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2242,plain,
% 3.16/0.99      ( k1_tops_1(sK2,sK3) = sK3 | v3_pre_topc(sK3,sK2) != iProver_top ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_1304,c_2235]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2264,plain,
% 3.16/0.99      ( ~ v3_pre_topc(sK3,sK2) | k1_tops_1(sK2,sK3) = sK3 ),
% 3.16/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2242]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3,plain,
% 3.16/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.16/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1600,plain,
% 3.16/0.99      ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 3.16/0.99      | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 3.16/0.99      | k1_tops_1(sK2,sK3) = sK3 ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_845,plain,
% 3.16/0.99      ( v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | k1_tops_1(sK2,X0) != X0
% 3.16/0.99      | ~ sP1_iProver_split ),
% 3.16/0.99      inference(splitting,
% 3.16/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.16/0.99                [c_528]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_846,plain,
% 3.16/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 3.16/0.99      inference(splitting,
% 3.16/0.99                [splitting(split),new_symbols(definition,[])],
% 3.16/0.99                [c_528]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_938,plain,
% 3.16/0.99      ( k1_tops_1(sK2,X0) != X0
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | v3_pre_topc(X0,sK2) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_845,c_846,c_844]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_939,plain,
% 3.16/0.99      ( v3_pre_topc(X0,sK2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | k1_tops_1(sK2,X0) != X0 ),
% 3.16/0.99      inference(renaming,[status(thm)],[c_938]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1540,plain,
% 3.16/0.99      ( v3_pre_topc(sK3,sK2)
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | k1_tops_1(sK2,sK3) != sK3 ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_939]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1541,plain,
% 3.16/0.99      ( k1_tops_1(sK2,sK3) != sK3
% 3.16/0.99      | v3_pre_topc(sK3,sK2) = iProver_top
% 3.16/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1540]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_11,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.16/0.99      | ~ l1_pre_topc(X1) ),
% 3.16/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_491,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.16/0.99      | sK2 != X1 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_492,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_491]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1529,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_492]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_9,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | ~ l1_pre_topc(X1) ),
% 3.16/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_515,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.16/0.99      | sK2 != X1 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_516,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | m1_subset_1(k1_tops_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1526,plain,
% 3.16/0.99      ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_516]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_31,plain,
% 3.16/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(contradiction,plain,
% 3.16/0.99      ( $false ),
% 3.16/0.99      inference(minisat,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_7628,c_3203,c_2936,c_2937,c_2938,c_2762,c_2690,c_2598,
% 3.16/0.99                 c_2595,c_2264,c_1600,c_1541,c_1529,c_1526,c_31,c_24]) ).
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  ------                               Statistics
% 3.16/0.99  
% 3.16/0.99  ------ General
% 3.16/0.99  
% 3.16/0.99  abstr_ref_over_cycles:                  0
% 3.16/0.99  abstr_ref_under_cycles:                 0
% 3.16/0.99  gc_basic_clause_elim:                   0
% 3.16/0.99  forced_gc_time:                         0
% 3.16/0.99  parsing_time:                           0.006
% 3.16/0.99  unif_index_cands_time:                  0.
% 3.16/0.99  unif_index_add_time:                    0.
% 3.16/0.99  orderings_time:                         0.
% 3.16/0.99  out_proof_time:                         0.01
% 3.16/0.99  total_time:                             0.206
% 3.16/0.99  num_of_symbols:                         51
% 3.16/0.99  num_of_terms:                           6559
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing
% 3.16/0.99  
% 3.16/0.99  num_of_splits:                          4
% 3.16/0.99  num_of_split_atoms:                     3
% 3.16/0.99  num_of_reused_defs:                     1
% 3.16/0.99  num_eq_ax_congr_red:                    19
% 3.16/0.99  num_of_sem_filtered_clauses:            4
% 3.16/0.99  num_of_subtypes:                        0
% 3.16/0.99  monotx_restored_types:                  0
% 3.16/0.99  sat_num_of_epr_types:                   0
% 3.16/0.99  sat_num_of_non_cyclic_types:            0
% 3.16/0.99  sat_guarded_non_collapsed_types:        0
% 3.16/0.99  num_pure_diseq_elim:                    0
% 3.16/0.99  simp_replaced_by:                       0
% 3.16/0.99  res_preprocessed:                       118
% 3.16/0.99  prep_upred:                             0
% 3.16/0.99  prep_unflattend:                        19
% 3.16/0.99  smt_new_axioms:                         0
% 3.16/0.99  pred_elim_cands:                        4
% 3.16/0.99  pred_elim:                              4
% 3.16/0.99  pred_elim_cl:                           4
% 3.16/0.99  pred_elim_cycles:                       6
% 3.16/0.99  merged_defs:                            0
% 3.16/0.99  merged_defs_ncl:                        0
% 3.16/0.99  bin_hyper_res:                          0
% 3.16/0.99  prep_cycles:                            4
% 3.16/0.99  pred_elim_time:                         0.005
% 3.16/0.99  splitting_time:                         0.
% 3.16/0.99  sem_filter_time:                        0.
% 3.16/0.99  monotx_time:                            0.
% 3.16/0.99  subtype_inf_time:                       0.
% 3.16/0.99  
% 3.16/0.99  ------ Problem properties
% 3.16/0.99  
% 3.16/0.99  clauses:                                27
% 3.16/0.99  conjectures:                            5
% 3.16/0.99  epr:                                    6
% 3.16/0.99  horn:                                   19
% 3.16/0.99  ground:                                 5
% 3.16/0.99  unary:                                  2
% 3.16/0.99  binary:                                 11
% 3.16/0.99  lits:                                   80
% 3.16/0.99  lits_eq:                                4
% 3.16/0.99  fd_pure:                                0
% 3.16/0.99  fd_pseudo:                              0
% 3.16/0.99  fd_cond:                                0
% 3.16/0.99  fd_pseudo_cond:                         1
% 3.16/0.99  ac_symbols:                             0
% 3.16/0.99  
% 3.16/0.99  ------ Propositional Solver
% 3.16/0.99  
% 3.16/0.99  prop_solver_calls:                      29
% 3.16/0.99  prop_fast_solver_calls:                 1315
% 3.16/0.99  smt_solver_calls:                       0
% 3.16/0.99  smt_fast_solver_calls:                  0
% 3.16/0.99  prop_num_of_clauses:                    2844
% 3.16/0.99  prop_preprocess_simplified:             7237
% 3.16/0.99  prop_fo_subsumed:                       57
% 3.16/0.99  prop_solver_time:                       0.
% 3.16/0.99  smt_solver_time:                        0.
% 3.16/0.99  smt_fast_solver_time:                   0.
% 3.16/0.99  prop_fast_solver_time:                  0.
% 3.16/0.99  prop_unsat_core_time:                   0.
% 3.16/0.99  
% 3.16/0.99  ------ QBF
% 3.16/0.99  
% 3.16/0.99  qbf_q_res:                              0
% 3.16/0.99  qbf_num_tautologies:                    0
% 3.16/0.99  qbf_prep_cycles:                        0
% 3.16/0.99  
% 3.16/0.99  ------ BMC1
% 3.16/0.99  
% 3.16/0.99  bmc1_current_bound:                     -1
% 3.16/0.99  bmc1_last_solved_bound:                 -1
% 3.16/0.99  bmc1_unsat_core_size:                   -1
% 3.16/0.99  bmc1_unsat_core_parents_size:           -1
% 3.16/0.99  bmc1_merge_next_fun:                    0
% 3.16/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation
% 3.16/0.99  
% 3.16/0.99  inst_num_of_clauses:                    809
% 3.16/0.99  inst_num_in_passive:                    204
% 3.16/0.99  inst_num_in_active:                     364
% 3.16/0.99  inst_num_in_unprocessed:                240
% 3.16/0.99  inst_num_of_loops:                      452
% 3.16/0.99  inst_num_of_learning_restarts:          0
% 3.16/0.99  inst_num_moves_active_passive:          83
% 3.16/0.99  inst_lit_activity:                      0
% 3.16/0.99  inst_lit_activity_moves:                0
% 3.16/0.99  inst_num_tautologies:                   0
% 3.16/0.99  inst_num_prop_implied:                  0
% 3.16/0.99  inst_num_existing_simplified:           0
% 3.16/0.99  inst_num_eq_res_simplified:             0
% 3.16/0.99  inst_num_child_elim:                    0
% 3.16/0.99  inst_num_of_dismatching_blockings:      172
% 3.16/0.99  inst_num_of_non_proper_insts:           637
% 3.16/0.99  inst_num_of_duplicates:                 0
% 3.16/0.99  inst_inst_num_from_inst_to_res:         0
% 3.16/0.99  inst_dismatching_checking_time:         0.
% 3.16/0.99  
% 3.16/0.99  ------ Resolution
% 3.16/0.99  
% 3.16/0.99  res_num_of_clauses:                     0
% 3.16/0.99  res_num_in_passive:                     0
% 3.16/0.99  res_num_in_active:                      0
% 3.16/0.99  res_num_of_loops:                       122
% 3.16/0.99  res_forward_subset_subsumed:            84
% 3.16/0.99  res_backward_subset_subsumed:           0
% 3.16/0.99  res_forward_subsumed:                   0
% 3.16/0.99  res_backward_subsumed:                  0
% 3.16/0.99  res_forward_subsumption_resolution:     0
% 3.16/0.99  res_backward_subsumption_resolution:    0
% 3.16/0.99  res_clause_to_clause_subsumption:       1028
% 3.16/0.99  res_orphan_elimination:                 0
% 3.16/0.99  res_tautology_del:                      45
% 3.16/0.99  res_num_eq_res_simplified:              0
% 3.16/0.99  res_num_sel_changes:                    0
% 3.16/0.99  res_moves_from_active_to_pass:          0
% 3.16/0.99  
% 3.16/0.99  ------ Superposition
% 3.16/0.99  
% 3.16/0.99  sup_time_total:                         0.
% 3.16/0.99  sup_time_generating:                    0.
% 3.16/0.99  sup_time_sim_full:                      0.
% 3.16/0.99  sup_time_sim_immed:                     0.
% 3.16/0.99  
% 3.16/0.99  sup_num_of_clauses:                     151
% 3.16/0.99  sup_num_in_active:                      86
% 3.16/0.99  sup_num_in_passive:                     65
% 3.16/0.99  sup_num_of_loops:                       90
% 3.16/0.99  sup_fw_superposition:                   152
% 3.16/0.99  sup_bw_superposition:                   38
% 3.16/0.99  sup_immediate_simplified:               32
% 3.16/0.99  sup_given_eliminated:                   1
% 3.16/0.99  comparisons_done:                       0
% 3.16/0.99  comparisons_avoided:                    0
% 3.16/0.99  
% 3.16/0.99  ------ Simplifications
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  sim_fw_subset_subsumed:                 12
% 3.16/0.99  sim_bw_subset_subsumed:                 7
% 3.16/0.99  sim_fw_subsumed:                        6
% 3.16/0.99  sim_bw_subsumed:                        1
% 3.16/0.99  sim_fw_subsumption_res:                 0
% 3.16/0.99  sim_bw_subsumption_res:                 0
% 3.16/0.99  sim_tautology_del:                      9
% 3.16/0.99  sim_eq_tautology_del:                   21
% 3.16/0.99  sim_eq_res_simp:                        0
% 3.16/0.99  sim_fw_demodulated:                     3
% 3.16/0.99  sim_bw_demodulated:                     0
% 3.16/0.99  sim_light_normalised:                   13
% 3.16/0.99  sim_joinable_taut:                      0
% 3.16/0.99  sim_joinable_simp:                      0
% 3.16/0.99  sim_ac_normalised:                      0
% 3.16/0.99  sim_smt_subsumption:                    0
% 3.16/0.99  
%------------------------------------------------------------------------------
