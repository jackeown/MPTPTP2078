%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:24 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 821 expanded)
%              Number of clauses        :   84 ( 174 expanded)
%              Number of leaves         :   15 ( 234 expanded)
%              Depth                    :   29
%              Number of atoms          :  666 (8425 expanded)
%              Number of equality atoms :  117 ( 215 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   32 (   3 average)
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

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f13])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f39])).

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
    inference(rectify,[],[f40])).

fof(f45,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK5(X4),X1)
        & m1_connsp_2(sK5(X4),X0,X4)
        & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f41,f45,f44,f43,f42])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X4] :
      ( m1_connsp_2(sK5(X4),sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | ~ m1_connsp_2(X3,sK2,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f72,plain,(
    ! [X4] :
      ( r1_tarski(sK5(X4),sK3)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1462,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1447,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1448,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_1445,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_23,negated_conjecture,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_414,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_415,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_419,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_27,c_26])).

cnf(c_606,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r2_hidden(X0,sK3)
    | X1 != X0
    | sK5(X0) != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_419])).

cnf(c_607,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v3_pre_topc(sK3,sK2)
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_24])).

cnf(c_612,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_1440,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK5(X0))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1461,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3483,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK5(X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1461])).

cnf(c_19,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK2,sK4)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_18,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_385,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_386,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_27,c_26])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_406,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_390,c_12])).

cnf(c_585,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X0)
    | ~ r1_tarski(X1,sK3)
    | X0 != X1
    | sK4 != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_406])).

cnf(c_586,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,X0)
    | ~ r1_tarski(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_1441,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,X0) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_2477,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_1441])).

cnf(c_20,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_43,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2021,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2024,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_2499,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2477,c_43,c_2024])).

cnf(c_1452,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3356,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_1452])).

cnf(c_7675,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK5(X0)),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3483,c_43,c_2024,c_2477,c_3356])).

cnf(c_7685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5(X1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r1_tarski(sK5(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_7675])).

cnf(c_8101,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,X1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_7685])).

cnf(c_8343,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,X1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8101,c_43,c_2024,c_2477,c_3356])).

cnf(c_8344,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r1_tarski(sK5(X1),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8343])).

cnf(c_8355,plain,
    ( r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_8344])).

cnf(c_22,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK5(X0),sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1449,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3736,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3356,c_1449])).

cnf(c_8402,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8355,c_43,c_2024,c_2477,c_3736])).

cnf(c_8403,plain,
    ( r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8402])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1463,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8410,plain,
    ( r2_hidden(sK0(X0,k1_tops_1(sK2,sK3)),sK3) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8403,c_1463])).

cnf(c_8563,plain,
    ( r1_tarski(sK3,k1_tops_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_8410])).

cnf(c_878,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1923,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k1_tops_1(sK2,sK3),X2)
    | X1 != X2
    | X0 != k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_3175,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK2,sK3),X0)
    | v3_pre_topc(sK3,sK2)
    | sK2 != X0
    | sK3 != k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_3177,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
    | v3_pre_topc(sK3,sK2)
    | sK2 != sK2
    | sK3 != k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3175])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1853,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK2,sK3))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),X0)
    | X0 = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2811,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | sK3 = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_2813,plain,
    ( sK3 = k1_tops_1(sK2,sK3)
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2811])).

cnf(c_2501,plain,
    ( ~ v3_pre_topc(sK3,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2499])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_1651,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1652,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_13,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_477,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_478,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_26])).

cnf(c_483,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_1648,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_91,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_87,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8563,c_3177,c_2813,c_2501,c_1652,c_1648,c_91,c_87,c_32,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.95/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.02  
% 2.95/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.95/1.02  
% 2.95/1.02  ------  iProver source info
% 2.95/1.02  
% 2.95/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.95/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.95/1.02  git: non_committed_changes: false
% 2.95/1.02  git: last_make_outside_of_git: false
% 2.95/1.02  
% 2.95/1.02  ------ 
% 2.95/1.02  
% 2.95/1.02  ------ Input Options
% 2.95/1.02  
% 2.95/1.02  --out_options                           all
% 2.95/1.02  --tptp_safe_out                         true
% 2.95/1.02  --problem_path                          ""
% 2.95/1.02  --include_path                          ""
% 2.95/1.02  --clausifier                            res/vclausify_rel
% 2.95/1.02  --clausifier_options                    --mode clausify
% 2.95/1.02  --stdin                                 false
% 2.95/1.02  --stats_out                             all
% 2.95/1.02  
% 2.95/1.02  ------ General Options
% 2.95/1.02  
% 2.95/1.02  --fof                                   false
% 2.95/1.02  --time_out_real                         305.
% 2.95/1.02  --time_out_virtual                      -1.
% 2.95/1.02  --symbol_type_check                     false
% 2.95/1.02  --clausify_out                          false
% 2.95/1.02  --sig_cnt_out                           false
% 2.95/1.02  --trig_cnt_out                          false
% 2.95/1.02  --trig_cnt_out_tolerance                1.
% 2.95/1.02  --trig_cnt_out_sk_spl                   false
% 2.95/1.02  --abstr_cl_out                          false
% 2.95/1.02  
% 2.95/1.02  ------ Global Options
% 2.95/1.02  
% 2.95/1.02  --schedule                              default
% 2.95/1.02  --add_important_lit                     false
% 2.95/1.02  --prop_solver_per_cl                    1000
% 2.95/1.02  --min_unsat_core                        false
% 2.95/1.02  --soft_assumptions                      false
% 2.95/1.02  --soft_lemma_size                       3
% 2.95/1.02  --prop_impl_unit_size                   0
% 2.95/1.02  --prop_impl_unit                        []
% 2.95/1.02  --share_sel_clauses                     true
% 2.95/1.02  --reset_solvers                         false
% 2.95/1.02  --bc_imp_inh                            [conj_cone]
% 2.95/1.02  --conj_cone_tolerance                   3.
% 2.95/1.02  --extra_neg_conj                        none
% 2.95/1.02  --large_theory_mode                     true
% 2.95/1.02  --prolific_symb_bound                   200
% 2.95/1.02  --lt_threshold                          2000
% 2.95/1.02  --clause_weak_htbl                      true
% 2.95/1.02  --gc_record_bc_elim                     false
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing Options
% 2.95/1.02  
% 2.95/1.02  --preprocessing_flag                    true
% 2.95/1.02  --time_out_prep_mult                    0.1
% 2.95/1.02  --splitting_mode                        input
% 2.95/1.02  --splitting_grd                         true
% 2.95/1.02  --splitting_cvd                         false
% 2.95/1.02  --splitting_cvd_svl                     false
% 2.95/1.02  --splitting_nvd                         32
% 2.95/1.02  --sub_typing                            true
% 2.95/1.02  --prep_gs_sim                           true
% 2.95/1.02  --prep_unflatten                        true
% 2.95/1.02  --prep_res_sim                          true
% 2.95/1.02  --prep_upred                            true
% 2.95/1.02  --prep_sem_filter                       exhaustive
% 2.95/1.02  --prep_sem_filter_out                   false
% 2.95/1.02  --pred_elim                             true
% 2.95/1.02  --res_sim_input                         true
% 2.95/1.02  --eq_ax_congr_red                       true
% 2.95/1.02  --pure_diseq_elim                       true
% 2.95/1.02  --brand_transform                       false
% 2.95/1.02  --non_eq_to_eq                          false
% 2.95/1.02  --prep_def_merge                        true
% 2.95/1.02  --prep_def_merge_prop_impl              false
% 2.95/1.02  --prep_def_merge_mbd                    true
% 2.95/1.02  --prep_def_merge_tr_red                 false
% 2.95/1.02  --prep_def_merge_tr_cl                  false
% 2.95/1.02  --smt_preprocessing                     true
% 2.95/1.02  --smt_ac_axioms                         fast
% 2.95/1.02  --preprocessed_out                      false
% 2.95/1.02  --preprocessed_stats                    false
% 2.95/1.02  
% 2.95/1.02  ------ Abstraction refinement Options
% 2.95/1.02  
% 2.95/1.02  --abstr_ref                             []
% 2.95/1.02  --abstr_ref_prep                        false
% 2.95/1.02  --abstr_ref_until_sat                   false
% 2.95/1.02  --abstr_ref_sig_restrict                funpre
% 2.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/1.02  --abstr_ref_under                       []
% 2.95/1.02  
% 2.95/1.02  ------ SAT Options
% 2.95/1.02  
% 2.95/1.02  --sat_mode                              false
% 2.95/1.02  --sat_fm_restart_options                ""
% 2.95/1.02  --sat_gr_def                            false
% 2.95/1.02  --sat_epr_types                         true
% 2.95/1.02  --sat_non_cyclic_types                  false
% 2.95/1.02  --sat_finite_models                     false
% 2.95/1.02  --sat_fm_lemmas                         false
% 2.95/1.02  --sat_fm_prep                           false
% 2.95/1.02  --sat_fm_uc_incr                        true
% 2.95/1.02  --sat_out_model                         small
% 2.95/1.02  --sat_out_clauses                       false
% 2.95/1.02  
% 2.95/1.02  ------ QBF Options
% 2.95/1.02  
% 2.95/1.02  --qbf_mode                              false
% 2.95/1.02  --qbf_elim_univ                         false
% 2.95/1.02  --qbf_dom_inst                          none
% 2.95/1.02  --qbf_dom_pre_inst                      false
% 2.95/1.02  --qbf_sk_in                             false
% 2.95/1.02  --qbf_pred_elim                         true
% 2.95/1.02  --qbf_split                             512
% 2.95/1.02  
% 2.95/1.02  ------ BMC1 Options
% 2.95/1.02  
% 2.95/1.02  --bmc1_incremental                      false
% 2.95/1.02  --bmc1_axioms                           reachable_all
% 2.95/1.02  --bmc1_min_bound                        0
% 2.95/1.02  --bmc1_max_bound                        -1
% 2.95/1.02  --bmc1_max_bound_default                -1
% 2.95/1.02  --bmc1_symbol_reachability              true
% 2.95/1.02  --bmc1_property_lemmas                  false
% 2.95/1.02  --bmc1_k_induction                      false
% 2.95/1.02  --bmc1_non_equiv_states                 false
% 2.95/1.02  --bmc1_deadlock                         false
% 2.95/1.02  --bmc1_ucm                              false
% 2.95/1.02  --bmc1_add_unsat_core                   none
% 2.95/1.02  --bmc1_unsat_core_children              false
% 2.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/1.02  --bmc1_out_stat                         full
% 2.95/1.02  --bmc1_ground_init                      false
% 2.95/1.02  --bmc1_pre_inst_next_state              false
% 2.95/1.02  --bmc1_pre_inst_state                   false
% 2.95/1.02  --bmc1_pre_inst_reach_state             false
% 2.95/1.02  --bmc1_out_unsat_core                   false
% 2.95/1.02  --bmc1_aig_witness_out                  false
% 2.95/1.02  --bmc1_verbose                          false
% 2.95/1.02  --bmc1_dump_clauses_tptp                false
% 2.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.95/1.02  --bmc1_dump_file                        -
% 2.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.95/1.02  --bmc1_ucm_extend_mode                  1
% 2.95/1.02  --bmc1_ucm_init_mode                    2
% 2.95/1.02  --bmc1_ucm_cone_mode                    none
% 2.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.95/1.02  --bmc1_ucm_relax_model                  4
% 2.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/1.02  --bmc1_ucm_layered_model                none
% 2.95/1.02  --bmc1_ucm_max_lemma_size               10
% 2.95/1.02  
% 2.95/1.02  ------ AIG Options
% 2.95/1.02  
% 2.95/1.02  --aig_mode                              false
% 2.95/1.02  
% 2.95/1.02  ------ Instantiation Options
% 2.95/1.02  
% 2.95/1.02  --instantiation_flag                    true
% 2.95/1.02  --inst_sos_flag                         false
% 2.95/1.02  --inst_sos_phase                        true
% 2.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/1.02  --inst_lit_sel_side                     num_symb
% 2.95/1.02  --inst_solver_per_active                1400
% 2.95/1.02  --inst_solver_calls_frac                1.
% 2.95/1.02  --inst_passive_queue_type               priority_queues
% 2.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/1.02  --inst_passive_queues_freq              [25;2]
% 2.95/1.02  --inst_dismatching                      true
% 2.95/1.02  --inst_eager_unprocessed_to_passive     true
% 2.95/1.02  --inst_prop_sim_given                   true
% 2.95/1.02  --inst_prop_sim_new                     false
% 2.95/1.02  --inst_subs_new                         false
% 2.95/1.02  --inst_eq_res_simp                      false
% 2.95/1.02  --inst_subs_given                       false
% 2.95/1.02  --inst_orphan_elimination               true
% 2.95/1.02  --inst_learning_loop_flag               true
% 2.95/1.02  --inst_learning_start                   3000
% 2.95/1.02  --inst_learning_factor                  2
% 2.95/1.02  --inst_start_prop_sim_after_learn       3
% 2.95/1.02  --inst_sel_renew                        solver
% 2.95/1.02  --inst_lit_activity_flag                true
% 2.95/1.02  --inst_restr_to_given                   false
% 2.95/1.02  --inst_activity_threshold               500
% 2.95/1.02  --inst_out_proof                        true
% 2.95/1.02  
% 2.95/1.02  ------ Resolution Options
% 2.95/1.02  
% 2.95/1.02  --resolution_flag                       true
% 2.95/1.02  --res_lit_sel                           adaptive
% 2.95/1.02  --res_lit_sel_side                      none
% 2.95/1.02  --res_ordering                          kbo
% 2.95/1.02  --res_to_prop_solver                    active
% 2.95/1.02  --res_prop_simpl_new                    false
% 2.95/1.02  --res_prop_simpl_given                  true
% 2.95/1.02  --res_passive_queue_type                priority_queues
% 2.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/1.02  --res_passive_queues_freq               [15;5]
% 2.95/1.02  --res_forward_subs                      full
% 2.95/1.02  --res_backward_subs                     full
% 2.95/1.02  --res_forward_subs_resolution           true
% 2.95/1.02  --res_backward_subs_resolution          true
% 2.95/1.02  --res_orphan_elimination                true
% 2.95/1.02  --res_time_limit                        2.
% 2.95/1.02  --res_out_proof                         true
% 2.95/1.02  
% 2.95/1.02  ------ Superposition Options
% 2.95/1.02  
% 2.95/1.02  --superposition_flag                    true
% 2.95/1.02  --sup_passive_queue_type                priority_queues
% 2.95/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.95/1.02  --demod_completeness_check              fast
% 2.95/1.02  --demod_use_ground                      true
% 2.95/1.02  --sup_to_prop_solver                    passive
% 2.95/1.02  --sup_prop_simpl_new                    true
% 2.95/1.02  --sup_prop_simpl_given                  true
% 2.95/1.02  --sup_fun_splitting                     false
% 2.95/1.02  --sup_smt_interval                      50000
% 2.95/1.02  
% 2.95/1.02  ------ Superposition Simplification Setup
% 2.95/1.02  
% 2.95/1.02  --sup_indices_passive                   []
% 2.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_full_bw                           [BwDemod]
% 2.95/1.02  --sup_immed_triv                        [TrivRules]
% 2.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_immed_bw_main                     []
% 2.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.02  
% 2.95/1.02  ------ Combination Options
% 2.95/1.02  
% 2.95/1.02  --comb_res_mult                         3
% 2.95/1.02  --comb_sup_mult                         2
% 2.95/1.02  --comb_inst_mult                        10
% 2.95/1.02  
% 2.95/1.02  ------ Debug Options
% 2.95/1.02  
% 2.95/1.02  --dbg_backtrace                         false
% 2.95/1.02  --dbg_dump_prop_clauses                 false
% 2.95/1.02  --dbg_dump_prop_clauses_file            -
% 2.95/1.02  --dbg_out_stat                          false
% 2.95/1.02  ------ Parsing...
% 2.95/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.95/1.02  ------ Proving...
% 2.95/1.02  ------ Problem Properties 
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  clauses                                 24
% 2.95/1.02  conjectures                             5
% 2.95/1.02  EPR                                     4
% 2.95/1.02  Horn                                    19
% 2.95/1.02  unary                                   2
% 2.95/1.02  binary                                  10
% 2.95/1.02  lits                                    66
% 2.95/1.02  lits eq                                 3
% 2.95/1.02  fd_pure                                 0
% 2.95/1.02  fd_pseudo                               0
% 2.95/1.02  fd_cond                                 0
% 2.95/1.02  fd_pseudo_cond                          3
% 2.95/1.02  AC symbols                              0
% 2.95/1.02  
% 2.95/1.02  ------ Schedule dynamic 5 is on 
% 2.95/1.02  
% 2.95/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  ------ 
% 2.95/1.02  Current options:
% 2.95/1.02  ------ 
% 2.95/1.02  
% 2.95/1.02  ------ Input Options
% 2.95/1.02  
% 2.95/1.02  --out_options                           all
% 2.95/1.02  --tptp_safe_out                         true
% 2.95/1.02  --problem_path                          ""
% 2.95/1.02  --include_path                          ""
% 2.95/1.02  --clausifier                            res/vclausify_rel
% 2.95/1.02  --clausifier_options                    --mode clausify
% 2.95/1.02  --stdin                                 false
% 2.95/1.02  --stats_out                             all
% 2.95/1.02  
% 2.95/1.02  ------ General Options
% 2.95/1.02  
% 2.95/1.02  --fof                                   false
% 2.95/1.02  --time_out_real                         305.
% 2.95/1.02  --time_out_virtual                      -1.
% 2.95/1.02  --symbol_type_check                     false
% 2.95/1.02  --clausify_out                          false
% 2.95/1.02  --sig_cnt_out                           false
% 2.95/1.02  --trig_cnt_out                          false
% 2.95/1.02  --trig_cnt_out_tolerance                1.
% 2.95/1.02  --trig_cnt_out_sk_spl                   false
% 2.95/1.02  --abstr_cl_out                          false
% 2.95/1.02  
% 2.95/1.02  ------ Global Options
% 2.95/1.02  
% 2.95/1.02  --schedule                              default
% 2.95/1.02  --add_important_lit                     false
% 2.95/1.02  --prop_solver_per_cl                    1000
% 2.95/1.02  --min_unsat_core                        false
% 2.95/1.02  --soft_assumptions                      false
% 2.95/1.02  --soft_lemma_size                       3
% 2.95/1.02  --prop_impl_unit_size                   0
% 2.95/1.02  --prop_impl_unit                        []
% 2.95/1.02  --share_sel_clauses                     true
% 2.95/1.02  --reset_solvers                         false
% 2.95/1.02  --bc_imp_inh                            [conj_cone]
% 2.95/1.02  --conj_cone_tolerance                   3.
% 2.95/1.02  --extra_neg_conj                        none
% 2.95/1.02  --large_theory_mode                     true
% 2.95/1.02  --prolific_symb_bound                   200
% 2.95/1.02  --lt_threshold                          2000
% 2.95/1.02  --clause_weak_htbl                      true
% 2.95/1.02  --gc_record_bc_elim                     false
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing Options
% 2.95/1.02  
% 2.95/1.02  --preprocessing_flag                    true
% 2.95/1.02  --time_out_prep_mult                    0.1
% 2.95/1.02  --splitting_mode                        input
% 2.95/1.02  --splitting_grd                         true
% 2.95/1.02  --splitting_cvd                         false
% 2.95/1.02  --splitting_cvd_svl                     false
% 2.95/1.02  --splitting_nvd                         32
% 2.95/1.02  --sub_typing                            true
% 2.95/1.02  --prep_gs_sim                           true
% 2.95/1.02  --prep_unflatten                        true
% 2.95/1.02  --prep_res_sim                          true
% 2.95/1.02  --prep_upred                            true
% 2.95/1.02  --prep_sem_filter                       exhaustive
% 2.95/1.02  --prep_sem_filter_out                   false
% 2.95/1.02  --pred_elim                             true
% 2.95/1.02  --res_sim_input                         true
% 2.95/1.02  --eq_ax_congr_red                       true
% 2.95/1.02  --pure_diseq_elim                       true
% 2.95/1.02  --brand_transform                       false
% 2.95/1.02  --non_eq_to_eq                          false
% 2.95/1.02  --prep_def_merge                        true
% 2.95/1.02  --prep_def_merge_prop_impl              false
% 2.95/1.02  --prep_def_merge_mbd                    true
% 2.95/1.02  --prep_def_merge_tr_red                 false
% 2.95/1.02  --prep_def_merge_tr_cl                  false
% 2.95/1.02  --smt_preprocessing                     true
% 2.95/1.02  --smt_ac_axioms                         fast
% 2.95/1.02  --preprocessed_out                      false
% 2.95/1.02  --preprocessed_stats                    false
% 2.95/1.02  
% 2.95/1.02  ------ Abstraction refinement Options
% 2.95/1.02  
% 2.95/1.02  --abstr_ref                             []
% 2.95/1.02  --abstr_ref_prep                        false
% 2.95/1.02  --abstr_ref_until_sat                   false
% 2.95/1.02  --abstr_ref_sig_restrict                funpre
% 2.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/1.02  --abstr_ref_under                       []
% 2.95/1.02  
% 2.95/1.02  ------ SAT Options
% 2.95/1.02  
% 2.95/1.02  --sat_mode                              false
% 2.95/1.02  --sat_fm_restart_options                ""
% 2.95/1.02  --sat_gr_def                            false
% 2.95/1.02  --sat_epr_types                         true
% 2.95/1.02  --sat_non_cyclic_types                  false
% 2.95/1.02  --sat_finite_models                     false
% 2.95/1.02  --sat_fm_lemmas                         false
% 2.95/1.02  --sat_fm_prep                           false
% 2.95/1.02  --sat_fm_uc_incr                        true
% 2.95/1.02  --sat_out_model                         small
% 2.95/1.02  --sat_out_clauses                       false
% 2.95/1.02  
% 2.95/1.02  ------ QBF Options
% 2.95/1.02  
% 2.95/1.02  --qbf_mode                              false
% 2.95/1.02  --qbf_elim_univ                         false
% 2.95/1.02  --qbf_dom_inst                          none
% 2.95/1.02  --qbf_dom_pre_inst                      false
% 2.95/1.02  --qbf_sk_in                             false
% 2.95/1.02  --qbf_pred_elim                         true
% 2.95/1.02  --qbf_split                             512
% 2.95/1.02  
% 2.95/1.02  ------ BMC1 Options
% 2.95/1.02  
% 2.95/1.02  --bmc1_incremental                      false
% 2.95/1.02  --bmc1_axioms                           reachable_all
% 2.95/1.02  --bmc1_min_bound                        0
% 2.95/1.02  --bmc1_max_bound                        -1
% 2.95/1.02  --bmc1_max_bound_default                -1
% 2.95/1.02  --bmc1_symbol_reachability              true
% 2.95/1.02  --bmc1_property_lemmas                  false
% 2.95/1.02  --bmc1_k_induction                      false
% 2.95/1.02  --bmc1_non_equiv_states                 false
% 2.95/1.02  --bmc1_deadlock                         false
% 2.95/1.02  --bmc1_ucm                              false
% 2.95/1.02  --bmc1_add_unsat_core                   none
% 2.95/1.02  --bmc1_unsat_core_children              false
% 2.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/1.02  --bmc1_out_stat                         full
% 2.95/1.02  --bmc1_ground_init                      false
% 2.95/1.02  --bmc1_pre_inst_next_state              false
% 2.95/1.02  --bmc1_pre_inst_state                   false
% 2.95/1.02  --bmc1_pre_inst_reach_state             false
% 2.95/1.02  --bmc1_out_unsat_core                   false
% 2.95/1.02  --bmc1_aig_witness_out                  false
% 2.95/1.02  --bmc1_verbose                          false
% 2.95/1.02  --bmc1_dump_clauses_tptp                false
% 2.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.95/1.02  --bmc1_dump_file                        -
% 2.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.95/1.02  --bmc1_ucm_extend_mode                  1
% 2.95/1.02  --bmc1_ucm_init_mode                    2
% 2.95/1.02  --bmc1_ucm_cone_mode                    none
% 2.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.95/1.02  --bmc1_ucm_relax_model                  4
% 2.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/1.02  --bmc1_ucm_layered_model                none
% 2.95/1.02  --bmc1_ucm_max_lemma_size               10
% 2.95/1.02  
% 2.95/1.02  ------ AIG Options
% 2.95/1.02  
% 2.95/1.02  --aig_mode                              false
% 2.95/1.02  
% 2.95/1.02  ------ Instantiation Options
% 2.95/1.02  
% 2.95/1.02  --instantiation_flag                    true
% 2.95/1.02  --inst_sos_flag                         false
% 2.95/1.02  --inst_sos_phase                        true
% 2.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/1.02  --inst_lit_sel_side                     none
% 2.95/1.02  --inst_solver_per_active                1400
% 2.95/1.02  --inst_solver_calls_frac                1.
% 2.95/1.02  --inst_passive_queue_type               priority_queues
% 2.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/1.02  --inst_passive_queues_freq              [25;2]
% 2.95/1.02  --inst_dismatching                      true
% 2.95/1.02  --inst_eager_unprocessed_to_passive     true
% 2.95/1.02  --inst_prop_sim_given                   true
% 2.95/1.02  --inst_prop_sim_new                     false
% 2.95/1.02  --inst_subs_new                         false
% 2.95/1.02  --inst_eq_res_simp                      false
% 2.95/1.02  --inst_subs_given                       false
% 2.95/1.02  --inst_orphan_elimination               true
% 2.95/1.02  --inst_learning_loop_flag               true
% 2.95/1.02  --inst_learning_start                   3000
% 2.95/1.02  --inst_learning_factor                  2
% 2.95/1.02  --inst_start_prop_sim_after_learn       3
% 2.95/1.02  --inst_sel_renew                        solver
% 2.95/1.02  --inst_lit_activity_flag                true
% 2.95/1.02  --inst_restr_to_given                   false
% 2.95/1.02  --inst_activity_threshold               500
% 2.95/1.02  --inst_out_proof                        true
% 2.95/1.02  
% 2.95/1.02  ------ Resolution Options
% 2.95/1.02  
% 2.95/1.02  --resolution_flag                       false
% 2.95/1.02  --res_lit_sel                           adaptive
% 2.95/1.02  --res_lit_sel_side                      none
% 2.95/1.02  --res_ordering                          kbo
% 2.95/1.02  --res_to_prop_solver                    active
% 2.95/1.02  --res_prop_simpl_new                    false
% 2.95/1.02  --res_prop_simpl_given                  true
% 2.95/1.02  --res_passive_queue_type                priority_queues
% 2.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/1.02  --res_passive_queues_freq               [15;5]
% 2.95/1.02  --res_forward_subs                      full
% 2.95/1.02  --res_backward_subs                     full
% 2.95/1.02  --res_forward_subs_resolution           true
% 2.95/1.02  --res_backward_subs_resolution          true
% 2.95/1.02  --res_orphan_elimination                true
% 2.95/1.02  --res_time_limit                        2.
% 2.95/1.02  --res_out_proof                         true
% 2.95/1.02  
% 2.95/1.02  ------ Superposition Options
% 2.95/1.02  
% 2.95/1.02  --superposition_flag                    true
% 2.95/1.02  --sup_passive_queue_type                priority_queues
% 2.95/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.95/1.02  --demod_completeness_check              fast
% 2.95/1.02  --demod_use_ground                      true
% 2.95/1.02  --sup_to_prop_solver                    passive
% 2.95/1.02  --sup_prop_simpl_new                    true
% 2.95/1.02  --sup_prop_simpl_given                  true
% 2.95/1.02  --sup_fun_splitting                     false
% 2.95/1.02  --sup_smt_interval                      50000
% 2.95/1.02  
% 2.95/1.02  ------ Superposition Simplification Setup
% 2.95/1.02  
% 2.95/1.02  --sup_indices_passive                   []
% 2.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_full_bw                           [BwDemod]
% 2.95/1.02  --sup_immed_triv                        [TrivRules]
% 2.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_immed_bw_main                     []
% 2.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.02  
% 2.95/1.02  ------ Combination Options
% 2.95/1.02  
% 2.95/1.02  --comb_res_mult                         3
% 2.95/1.02  --comb_sup_mult                         2
% 2.95/1.02  --comb_inst_mult                        10
% 2.95/1.02  
% 2.95/1.02  ------ Debug Options
% 2.95/1.02  
% 2.95/1.02  --dbg_backtrace                         false
% 2.95/1.02  --dbg_dump_prop_clauses                 false
% 2.95/1.02  --dbg_dump_prop_clauses_file            -
% 2.95/1.02  --dbg_out_stat                          false
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  ------ Proving...
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  % SZS status Theorem for theBenchmark.p
% 2.95/1.02  
% 2.95/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.95/1.02  
% 2.95/1.02  fof(f1,axiom,(
% 2.95/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f13,plain,(
% 2.95/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.95/1.02    inference(ennf_transformation,[],[f1])).
% 2.95/1.02  
% 2.95/1.02  fof(f27,plain,(
% 2.95/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.95/1.02    inference(nnf_transformation,[],[f13])).
% 2.95/1.02  
% 2.95/1.02  fof(f28,plain,(
% 2.95/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.95/1.02    inference(rectify,[],[f27])).
% 2.95/1.02  
% 2.95/1.02  fof(f29,plain,(
% 2.95/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.95/1.02    introduced(choice_axiom,[])).
% 2.95/1.02  
% 2.95/1.02  fof(f30,plain,(
% 2.95/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.95/1.02  
% 2.95/1.02  fof(f48,plain,(
% 2.95/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f30])).
% 2.95/1.02  
% 2.95/1.02  fof(f11,conjecture,(
% 2.95/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f12,negated_conjecture,(
% 2.95/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.95/1.02    inference(negated_conjecture,[],[f11])).
% 2.95/1.02  
% 2.95/1.02  fof(f25,plain,(
% 2.95/1.02    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.95/1.02    inference(ennf_transformation,[],[f12])).
% 2.95/1.02  
% 2.95/1.02  fof(f26,plain,(
% 2.95/1.02    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.95/1.02    inference(flattening,[],[f25])).
% 2.95/1.02  
% 2.95/1.02  fof(f39,plain,(
% 2.95/1.02    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.95/1.02    inference(nnf_transformation,[],[f26])).
% 2.95/1.02  
% 2.95/1.02  fof(f40,plain,(
% 2.95/1.02    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.95/1.02    inference(flattening,[],[f39])).
% 2.95/1.02  
% 2.95/1.02  fof(f41,plain,(
% 2.95/1.02    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.95/1.02    inference(rectify,[],[f40])).
% 2.95/1.02  
% 2.95/1.02  fof(f45,plain,(
% 2.95/1.02    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK5(X4),X1) & m1_connsp_2(sK5(X4),X0,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.95/1.02    introduced(choice_axiom,[])).
% 2.95/1.02  
% 2.95/1.02  fof(f44,plain,(
% 2.95/1.02    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.95/1.02    introduced(choice_axiom,[])).
% 2.95/1.02  
% 2.95/1.02  fof(f43,plain,(
% 2.95/1.02    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK3,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK3) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.95/1.02    introduced(choice_axiom,[])).
% 2.95/1.02  
% 2.95/1.02  fof(f42,plain,(
% 2.95/1.02    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK2,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.95/1.02    introduced(choice_axiom,[])).
% 2.95/1.02  
% 2.95/1.02  fof(f46,plain,(
% 2.95/1.02    (((! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) & (! [X4] : ((r1_tarski(sK5(X4),sK3) & m1_connsp_2(sK5(X4),sK2,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f41,f45,f44,f43,f42])).
% 2.95/1.02  
% 2.95/1.02  fof(f69,plain,(
% 2.95/1.02    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f70,plain,(
% 2.95/1.02    ( ! [X4] : (m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f8,axiom,(
% 2.95/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f19,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.95/1.02    inference(ennf_transformation,[],[f8])).
% 2.95/1.02  
% 2.95/1.02  fof(f20,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.95/1.02    inference(flattening,[],[f19])).
% 2.95/1.02  
% 2.95/1.02  fof(f62,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f20])).
% 2.95/1.02  
% 2.95/1.02  fof(f68,plain,(
% 2.95/1.02    l1_pre_topc(sK2)),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f71,plain,(
% 2.95/1.02    ( ! [X4] : (m1_connsp_2(sK5(X4),sK2,X4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f9,axiom,(
% 2.95/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f21,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.95/1.02    inference(ennf_transformation,[],[f9])).
% 2.95/1.02  
% 2.95/1.02  fof(f22,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.95/1.02    inference(flattening,[],[f21])).
% 2.95/1.02  
% 2.95/1.02  fof(f38,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.95/1.02    inference(nnf_transformation,[],[f22])).
% 2.95/1.02  
% 2.95/1.02  fof(f63,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f38])).
% 2.95/1.02  
% 2.95/1.02  fof(f66,plain,(
% 2.95/1.02    ~v2_struct_0(sK2)),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f67,plain,(
% 2.95/1.02    v2_pre_topc(sK2)),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f47,plain,(
% 2.95/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f30])).
% 2.95/1.02  
% 2.95/1.02  fof(f75,plain,(
% 2.95/1.02    ( ! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f10,axiom,(
% 2.95/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f23,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.95/1.02    inference(ennf_transformation,[],[f10])).
% 2.95/1.02  
% 2.95/1.02  fof(f24,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.95/1.02    inference(flattening,[],[f23])).
% 2.95/1.02  
% 2.95/1.02  fof(f65,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f24])).
% 2.95/1.02  
% 2.95/1.02  fof(f5,axiom,(
% 2.95/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f14,plain,(
% 2.95/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.95/1.02    inference(ennf_transformation,[],[f5])).
% 2.95/1.02  
% 2.95/1.02  fof(f15,plain,(
% 2.95/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.95/1.02    inference(flattening,[],[f14])).
% 2.95/1.02  
% 2.95/1.02  fof(f59,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f15])).
% 2.95/1.02  
% 2.95/1.02  fof(f74,plain,(
% 2.95/1.02    r2_hidden(sK4,sK3) | ~v3_pre_topc(sK3,sK2)),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f2,axiom,(
% 2.95/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f31,plain,(
% 2.95/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.95/1.02    inference(nnf_transformation,[],[f2])).
% 2.95/1.02  
% 2.95/1.02  fof(f32,plain,(
% 2.95/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.95/1.02    inference(flattening,[],[f31])).
% 2.95/1.02  
% 2.95/1.02  fof(f50,plain,(
% 2.95/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.95/1.02    inference(cnf_transformation,[],[f32])).
% 2.95/1.02  
% 2.95/1.02  fof(f77,plain,(
% 2.95/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.95/1.02    inference(equality_resolution,[],[f50])).
% 2.95/1.02  
% 2.95/1.02  fof(f72,plain,(
% 2.95/1.02    ( ! [X4] : (r1_tarski(sK5(X4),sK3) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f49,plain,(
% 2.95/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f30])).
% 2.95/1.02  
% 2.95/1.02  fof(f52,plain,(
% 2.95/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f32])).
% 2.95/1.02  
% 2.95/1.02  fof(f7,axiom,(
% 2.95/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f18,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.95/1.02    inference(ennf_transformation,[],[f7])).
% 2.95/1.02  
% 2.95/1.02  fof(f61,plain,(
% 2.95/1.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f18])).
% 2.95/1.02  
% 2.95/1.02  fof(f6,axiom,(
% 2.95/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f16,plain,(
% 2.95/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.95/1.02    inference(ennf_transformation,[],[f6])).
% 2.95/1.02  
% 2.95/1.02  fof(f17,plain,(
% 2.95/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.95/1.02    inference(flattening,[],[f16])).
% 2.95/1.02  
% 2.95/1.02  fof(f60,plain,(
% 2.95/1.02    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f17])).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1,plain,
% 2.95/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1462,plain,
% 2.95/1.02      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.95/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_25,negated_conjecture,
% 2.95/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.95/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1447,plain,
% 2.95/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_24,negated_conjecture,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.95/1.02      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ r2_hidden(X0,sK3) ),
% 2.95/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1448,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) = iProver_top
% 2.95/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.95/1.02      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_15,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | ~ r1_tarski(X0,X2)
% 2.95/1.02      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.95/1.02      | ~ l1_pre_topc(X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_26,negated_conjecture,
% 2.95/1.02      ( l1_pre_topc(sK2) ),
% 2.95/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_498,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | ~ r1_tarski(X0,X2)
% 2.95/1.02      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.95/1.02      | sK2 != X1 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_499,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ r1_tarski(X1,X0)
% 2.95/1.02      | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_498]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1445,plain,
% 2.95/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | r1_tarski(X1,X0) != iProver_top
% 2.95/1.02      | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_23,negated_conjecture,
% 2.95/1.02      ( m1_connsp_2(sK5(X0),sK2,X0)
% 2.95/1.02      | v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.95/1.02      | ~ r2_hidden(X0,sK3) ),
% 2.95/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_17,plain,
% 2.95/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 2.95/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.95/1.02      | v2_struct_0(X1)
% 2.95/1.02      | ~ v2_pre_topc(X1)
% 2.95/1.02      | ~ l1_pre_topc(X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_28,negated_conjecture,
% 2.95/1.02      ( ~ v2_struct_0(sK2) ),
% 2.95/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_414,plain,
% 2.95/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 2.95/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.95/1.02      | ~ v2_pre_topc(X1)
% 2.95/1.02      | ~ l1_pre_topc(X1)
% 2.95/1.02      | sK2 != X1 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_415,plain,
% 2.95/1.02      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.95/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 2.95/1.02      | ~ v2_pre_topc(sK2)
% 2.95/1.02      | ~ l1_pre_topc(sK2) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_414]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_27,negated_conjecture,
% 2.95/1.02      ( v2_pre_topc(sK2) ),
% 2.95/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_419,plain,
% 2.95/1.02      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.95/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_415,c_27,c_26]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_606,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.95/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.95/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 2.95/1.02      | ~ r2_hidden(X0,sK3)
% 2.95/1.02      | X1 != X0
% 2.95/1.02      | sK5(X0) != X2
% 2.95/1.02      | sK2 != sK2 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_419]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_607,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.95/1.02      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 2.95/1.02      | ~ r2_hidden(X0,sK3) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_606]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_611,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.95/1.02      | v3_pre_topc(sK3,sK2)
% 2.95/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 2.95/1.02      | ~ r2_hidden(X0,sK3) ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_607,c_24]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_612,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.95/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0)))
% 2.95/1.02      | ~ r2_hidden(X0,sK3) ),
% 2.95/1.02      inference(renaming,[status(thm)],[c_611]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1440,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) = iProver_top
% 2.95/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.95/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK5(X0))) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2,plain,
% 2.95/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.95/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1461,plain,
% 2.95/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.95/1.02      | r2_hidden(X0,X2) = iProver_top
% 2.95/1.02      | r1_tarski(X1,X2) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3483,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) = iProver_top
% 2.95/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.95/1.02      | r2_hidden(X0,X1) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(k1_tops_1(sK2,sK5(X0)),X1) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1440,c_1461]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_19,negated_conjecture,
% 2.95/1.02      ( ~ m1_connsp_2(X0,sK2,sK4)
% 2.95/1.02      | ~ v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ r1_tarski(X0,sK3) ),
% 2.95/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_18,plain,
% 2.95/1.02      ( m1_connsp_2(X0,X1,X2)
% 2.95/1.02      | ~ v3_pre_topc(X0,X1)
% 2.95/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | ~ r2_hidden(X2,X0)
% 2.95/1.02      | v2_struct_0(X1)
% 2.95/1.02      | ~ v2_pre_topc(X1)
% 2.95/1.02      | ~ l1_pre_topc(X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_385,plain,
% 2.95/1.02      ( m1_connsp_2(X0,X1,X2)
% 2.95/1.02      | ~ v3_pre_topc(X0,X1)
% 2.95/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | ~ r2_hidden(X2,X0)
% 2.95/1.02      | ~ v2_pre_topc(X1)
% 2.95/1.02      | ~ l1_pre_topc(X1)
% 2.95/1.02      | sK2 != X1 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_386,plain,
% 2.95/1.02      ( m1_connsp_2(X0,sK2,X1)
% 2.95/1.02      | ~ v3_pre_topc(X0,sK2)
% 2.95/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ r2_hidden(X1,X0)
% 2.95/1.02      | ~ v2_pre_topc(sK2)
% 2.95/1.02      | ~ l1_pre_topc(sK2) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_385]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_390,plain,
% 2.95/1.02      ( m1_connsp_2(X0,sK2,X1)
% 2.95/1.02      | ~ v3_pre_topc(X0,sK2)
% 2.95/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ r2_hidden(X1,X0) ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_386,c_27,c_26]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_12,plain,
% 2.95/1.02      ( m1_subset_1(X0,X1)
% 2.95/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.95/1.02      | ~ r2_hidden(X0,X2) ),
% 2.95/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_406,plain,
% 2.95/1.02      ( m1_connsp_2(X0,sK2,X1)
% 2.95/1.02      | ~ v3_pre_topc(X0,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ r2_hidden(X1,X0) ),
% 2.95/1.02      inference(forward_subsumption_resolution,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_390,c_12]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_585,plain,
% 2.95/1.02      ( ~ v3_pre_topc(X0,sK2)
% 2.95/1.02      | ~ v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ r2_hidden(X2,X0)
% 2.95/1.02      | ~ r1_tarski(X1,sK3)
% 2.95/1.02      | X0 != X1
% 2.95/1.02      | sK4 != X2
% 2.95/1.02      | sK2 != sK2 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_406]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_586,plain,
% 2.95/1.02      ( ~ v3_pre_topc(X0,sK2)
% 2.95/1.02      | ~ v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ r2_hidden(sK4,X0)
% 2.95/1.02      | ~ r1_tarski(X0,sK3) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_585]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1441,plain,
% 2.95/1.02      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.95/1.02      | v3_pre_topc(sK3,sK2) != iProver_top
% 2.95/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | r2_hidden(sK4,X0) != iProver_top
% 2.95/1.02      | r1_tarski(X0,sK3) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2477,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) != iProver_top
% 2.95/1.02      | r2_hidden(sK4,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK3,sK3) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1447,c_1441]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_20,negated_conjecture,
% 2.95/1.02      ( ~ v3_pre_topc(sK3,sK2) | r2_hidden(sK4,sK3) ),
% 2.95/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_43,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) != iProver_top
% 2.95/1.02      | r2_hidden(sK4,sK3) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_5,plain,
% 2.95/1.02      ( r1_tarski(X0,X0) ),
% 2.95/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2021,plain,
% 2.95/1.02      ( r1_tarski(sK3,sK3) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2024,plain,
% 2.95/1.02      ( r1_tarski(sK3,sK3) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2499,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) != iProver_top ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_2477,c_43,c_2024]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1452,plain,
% 2.95/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 2.95/1.02      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.95/1.02      | r2_hidden(X0,X2) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3356,plain,
% 2.95/1.02      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1447,c_1452]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_7675,plain,
% 2.95/1.02      ( r2_hidden(X0,X1) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(k1_tops_1(sK2,sK5(X0)),X1) != iProver_top ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_3483,c_43,c_2024,c_2477,c_3356]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_7685,plain,
% 2.95/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | m1_subset_1(sK5(X1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 2.95/1.02      | r2_hidden(X1,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK5(X1),X0) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1445,c_7675]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8101,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) = iProver_top
% 2.95/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.95/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | r2_hidden(X0,k1_tops_1(sK2,X1)) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK5(X0),X1) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1448,c_7685]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8343,plain,
% 2.95/1.02      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | r2_hidden(X0,k1_tops_1(sK2,X1)) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK5(X0),X1) != iProver_top ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_8101,c_43,c_2024,c_2477,c_3356]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8344,plain,
% 2.95/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 2.95/1.02      | r2_hidden(X1,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK5(X1),X0) != iProver_top ),
% 2.95/1.02      inference(renaming,[status(thm)],[c_8343]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8355,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK5(X0),sK3) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1447,c_8344]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_22,negated_conjecture,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.95/1.02      | ~ r2_hidden(X0,sK3)
% 2.95/1.02      | r1_tarski(sK5(X0),sK3) ),
% 2.95/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1449,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) = iProver_top
% 2.95/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK5(X0),sK3) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3736,plain,
% 2.95/1.02      ( v3_pre_topc(sK3,sK2) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK5(X0),sK3) = iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_3356,c_1449]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8402,plain,
% 2.95/1.02      ( r2_hidden(X0,sK3) != iProver_top
% 2.95/1.02      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_8355,c_43,c_2024,c_2477,c_3736]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8403,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 2.95/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 2.95/1.02      inference(renaming,[status(thm)],[c_8402]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_0,plain,
% 2.95/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1463,plain,
% 2.95/1.02      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.95/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8410,plain,
% 2.95/1.02      ( r2_hidden(sK0(X0,k1_tops_1(sK2,sK3)),sK3) != iProver_top
% 2.95/1.02      | r1_tarski(X0,k1_tops_1(sK2,sK3)) = iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_8403,c_1463]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8563,plain,
% 2.95/1.02      ( r1_tarski(sK3,k1_tops_1(sK2,sK3)) = iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1462,c_8410]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_878,plain,
% 2.95/1.02      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.95/1.02      theory(equality) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1923,plain,
% 2.95/1.02      ( v3_pre_topc(X0,X1)
% 2.95/1.02      | ~ v3_pre_topc(k1_tops_1(sK2,sK3),X2)
% 2.95/1.02      | X1 != X2
% 2.95/1.02      | X0 != k1_tops_1(sK2,sK3) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_878]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3175,plain,
% 2.95/1.02      ( ~ v3_pre_topc(k1_tops_1(sK2,sK3),X0)
% 2.95/1.02      | v3_pre_topc(sK3,sK2)
% 2.95/1.02      | sK2 != X0
% 2.95/1.02      | sK3 != k1_tops_1(sK2,sK3) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_1923]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3177,plain,
% 2.95/1.02      ( ~ v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
% 2.95/1.02      | v3_pre_topc(sK3,sK2)
% 2.95/1.02      | sK2 != sK2
% 2.95/1.02      | sK3 != k1_tops_1(sK2,sK3) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_3175]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3,plain,
% 2.95/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.95/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1853,plain,
% 2.95/1.02      ( ~ r1_tarski(X0,k1_tops_1(sK2,sK3))
% 2.95/1.02      | ~ r1_tarski(k1_tops_1(sK2,sK3),X0)
% 2.95/1.02      | X0 = k1_tops_1(sK2,sK3) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2811,plain,
% 2.95/1.02      ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 2.95/1.02      | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 2.95/1.02      | sK3 = k1_tops_1(sK2,sK3) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_1853]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2813,plain,
% 2.95/1.02      ( sK3 = k1_tops_1(sK2,sK3)
% 2.95/1.02      | r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top
% 2.95/1.02      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2811]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2501,plain,
% 2.95/1.02      ( ~ v3_pre_topc(sK3,sK2) ),
% 2.95/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2499]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_14,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.95/1.02      | ~ l1_pre_topc(X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_516,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.95/1.02      | sK2 != X1 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_517,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_516]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1651,plain,
% 2.95/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_517]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1652,plain,
% 2.95/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.95/1.02      | r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_13,plain,
% 2.95/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.95/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.95/1.02      | ~ v2_pre_topc(X0)
% 2.95/1.02      | ~ l1_pre_topc(X0) ),
% 2.95/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_477,plain,
% 2.95/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.95/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.95/1.02      | ~ l1_pre_topc(X0)
% 2.95/1.02      | sK2 != X0 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_478,plain,
% 2.95/1.02      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | ~ l1_pre_topc(sK2) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_477]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_482,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.95/1.02      | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_478,c_26]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_483,plain,
% 2.95/1.02      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.95/1.02      inference(renaming,[status(thm)],[c_482]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1648,plain,
% 2.95/1.02      ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
% 2.95/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_483]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_91,plain,
% 2.95/1.02      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_87,plain,
% 2.95/1.02      ( r1_tarski(sK2,sK2) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_32,plain,
% 2.95/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(contradiction,plain,
% 2.95/1.02      ( $false ),
% 2.95/1.02      inference(minisat,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_8563,c_3177,c_2813,c_2501,c_1652,c_1648,c_91,c_87,
% 2.95/1.02                 c_32,c_25]) ).
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.95/1.02  
% 2.95/1.02  ------                               Statistics
% 2.95/1.02  
% 2.95/1.02  ------ General
% 2.95/1.02  
% 2.95/1.02  abstr_ref_over_cycles:                  0
% 2.95/1.02  abstr_ref_under_cycles:                 0
% 2.95/1.02  gc_basic_clause_elim:                   0
% 2.95/1.02  forced_gc_time:                         0
% 2.95/1.02  parsing_time:                           0.009
% 2.95/1.02  unif_index_cands_time:                  0.
% 2.95/1.02  unif_index_add_time:                    0.
% 2.95/1.02  orderings_time:                         0.
% 2.95/1.02  out_proof_time:                         0.013
% 2.95/1.02  total_time:                             0.247
% 2.95/1.02  num_of_symbols:                         48
% 2.95/1.02  num_of_terms:                           5974
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing
% 2.95/1.02  
% 2.95/1.02  num_of_splits:                          0
% 2.95/1.02  num_of_split_atoms:                     0
% 2.95/1.02  num_of_reused_defs:                     0
% 2.95/1.02  num_eq_ax_congr_red:                    17
% 2.95/1.02  num_of_sem_filtered_clauses:            1
% 2.95/1.02  num_of_subtypes:                        0
% 2.95/1.02  monotx_restored_types:                  0
% 2.95/1.02  sat_num_of_epr_types:                   0
% 2.95/1.02  sat_num_of_non_cyclic_types:            0
% 2.95/1.02  sat_guarded_non_collapsed_types:        0
% 2.95/1.02  num_pure_diseq_elim:                    0
% 2.95/1.02  simp_replaced_by:                       0
% 2.95/1.02  res_preprocessed:                       119
% 2.95/1.02  prep_upred:                             0
% 2.95/1.02  prep_unflattend:                        14
% 2.95/1.02  smt_new_axioms:                         0
% 2.95/1.02  pred_elim_cands:                        4
% 2.95/1.02  pred_elim:                              4
% 2.95/1.02  pred_elim_cl:                           4
% 2.95/1.02  pred_elim_cycles:                       6
% 2.95/1.02  merged_defs:                            16
% 2.95/1.02  merged_defs_ncl:                        0
% 2.95/1.02  bin_hyper_res:                          16
% 2.95/1.02  prep_cycles:                            4
% 2.95/1.02  pred_elim_time:                         0.007
% 2.95/1.02  splitting_time:                         0.
% 2.95/1.02  sem_filter_time:                        0.
% 2.95/1.02  monotx_time:                            0.
% 2.95/1.02  subtype_inf_time:                       0.
% 2.95/1.02  
% 2.95/1.02  ------ Problem properties
% 2.95/1.02  
% 2.95/1.02  clauses:                                24
% 2.95/1.02  conjectures:                            5
% 2.95/1.02  epr:                                    4
% 2.95/1.02  horn:                                   19
% 2.95/1.02  ground:                                 3
% 2.95/1.02  unary:                                  2
% 2.95/1.02  binary:                                 10
% 2.95/1.02  lits:                                   66
% 2.95/1.02  lits_eq:                                3
% 2.95/1.02  fd_pure:                                0
% 2.95/1.02  fd_pseudo:                              0
% 2.95/1.02  fd_cond:                                0
% 2.95/1.02  fd_pseudo_cond:                         3
% 2.95/1.02  ac_symbols:                             0
% 2.95/1.02  
% 2.95/1.02  ------ Propositional Solver
% 2.95/1.02  
% 2.95/1.02  prop_solver_calls:                      28
% 2.95/1.02  prop_fast_solver_calls:                 1204
% 2.95/1.02  smt_solver_calls:                       0
% 2.95/1.02  smt_fast_solver_calls:                  0
% 2.95/1.02  prop_num_of_clauses:                    2927
% 2.95/1.02  prop_preprocess_simplified:             7872
% 2.95/1.02  prop_fo_subsumed:                       48
% 2.95/1.02  prop_solver_time:                       0.
% 2.95/1.02  smt_solver_time:                        0.
% 2.95/1.02  smt_fast_solver_time:                   0.
% 2.95/1.02  prop_fast_solver_time:                  0.
% 2.95/1.02  prop_unsat_core_time:                   0.
% 2.95/1.02  
% 2.95/1.02  ------ QBF
% 2.95/1.02  
% 2.95/1.02  qbf_q_res:                              0
% 2.95/1.02  qbf_num_tautologies:                    0
% 2.95/1.02  qbf_prep_cycles:                        0
% 2.95/1.02  
% 2.95/1.02  ------ BMC1
% 2.95/1.02  
% 2.95/1.02  bmc1_current_bound:                     -1
% 2.95/1.02  bmc1_last_solved_bound:                 -1
% 2.95/1.02  bmc1_unsat_core_size:                   -1
% 2.95/1.02  bmc1_unsat_core_parents_size:           -1
% 2.95/1.02  bmc1_merge_next_fun:                    0
% 2.95/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.95/1.02  
% 2.95/1.02  ------ Instantiation
% 2.95/1.02  
% 2.95/1.02  inst_num_of_clauses:                    741
% 2.95/1.02  inst_num_in_passive:                    300
% 2.95/1.02  inst_num_in_active:                     306
% 2.95/1.02  inst_num_in_unprocessed:                136
% 2.95/1.02  inst_num_of_loops:                      460
% 2.95/1.02  inst_num_of_learning_restarts:          0
% 2.95/1.02  inst_num_moves_active_passive:          151
% 2.95/1.02  inst_lit_activity:                      0
% 2.95/1.02  inst_lit_activity_moves:                0
% 2.95/1.02  inst_num_tautologies:                   0
% 2.95/1.02  inst_num_prop_implied:                  0
% 2.95/1.02  inst_num_existing_simplified:           0
% 2.95/1.02  inst_num_eq_res_simplified:             0
% 2.95/1.02  inst_num_child_elim:                    0
% 2.95/1.02  inst_num_of_dismatching_blockings:      310
% 2.95/1.02  inst_num_of_non_proper_insts:           941
% 2.95/1.02  inst_num_of_duplicates:                 0
% 2.95/1.02  inst_inst_num_from_inst_to_res:         0
% 2.95/1.02  inst_dismatching_checking_time:         0.
% 2.95/1.02  
% 2.95/1.02  ------ Resolution
% 2.95/1.02  
% 2.95/1.02  res_num_of_clauses:                     0
% 2.95/1.02  res_num_in_passive:                     0
% 2.95/1.02  res_num_in_active:                      0
% 2.95/1.02  res_num_of_loops:                       123
% 2.95/1.02  res_forward_subset_subsumed:            86
% 2.95/1.02  res_backward_subset_subsumed:           2
% 2.95/1.02  res_forward_subsumed:                   0
% 2.95/1.02  res_backward_subsumed:                  0
% 2.95/1.02  res_forward_subsumption_resolution:     2
% 2.95/1.02  res_backward_subsumption_resolution:    0
% 2.95/1.02  res_clause_to_clause_subsumption:       926
% 2.95/1.02  res_orphan_elimination:                 0
% 2.95/1.02  res_tautology_del:                      62
% 2.95/1.02  res_num_eq_res_simplified:              0
% 2.95/1.02  res_num_sel_changes:                    0
% 2.95/1.02  res_moves_from_active_to_pass:          0
% 2.95/1.02  
% 2.95/1.02  ------ Superposition
% 2.95/1.02  
% 2.95/1.02  sup_time_total:                         0.
% 2.95/1.02  sup_time_generating:                    0.
% 2.95/1.02  sup_time_sim_full:                      0.
% 2.95/1.02  sup_time_sim_immed:                     0.
% 2.95/1.02  
% 2.95/1.02  sup_num_of_clauses:                     145
% 2.95/1.02  sup_num_in_active:                      88
% 2.95/1.02  sup_num_in_passive:                     57
% 2.95/1.02  sup_num_of_loops:                       91
% 2.95/1.02  sup_fw_superposition:                   99
% 2.95/1.02  sup_bw_superposition:                   70
% 2.95/1.02  sup_immediate_simplified:               12
% 2.95/1.02  sup_given_eliminated:                   0
% 2.95/1.02  comparisons_done:                       0
% 2.95/1.02  comparisons_avoided:                    5
% 2.95/1.02  
% 2.95/1.02  ------ Simplifications
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  sim_fw_subset_subsumed:                 5
% 2.95/1.02  sim_bw_subset_subsumed:                 11
% 2.95/1.02  sim_fw_subsumed:                        5
% 2.95/1.02  sim_bw_subsumed:                        0
% 2.95/1.02  sim_fw_subsumption_res:                 3
% 2.95/1.02  sim_bw_subsumption_res:                 0
% 2.95/1.02  sim_tautology_del:                      12
% 2.95/1.02  sim_eq_tautology_del:                   5
% 2.95/1.02  sim_eq_res_simp:                        0
% 2.95/1.02  sim_fw_demodulated:                     0
% 2.95/1.02  sim_bw_demodulated:                     0
% 2.95/1.02  sim_light_normalised:                   0
% 2.95/1.02  sim_joinable_taut:                      0
% 2.95/1.02  sim_joinable_simp:                      0
% 2.95/1.02  sim_ac_normalised:                      0
% 2.95/1.02  sim_smt_subsumption:                    0
% 2.95/1.02  
%------------------------------------------------------------------------------
