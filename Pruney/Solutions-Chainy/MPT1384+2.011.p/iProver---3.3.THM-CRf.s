%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:26 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  186 (1303 expanded)
%              Number of clauses        :  122 ( 301 expanded)
%              Number of leaves         :   19 ( 364 expanded)
%              Depth                    :   31
%              Number of atoms          :  852 (13186 expanded)
%              Number of equality atoms :  199 ( 401 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f50,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK4(X4),X1)
        & m1_connsp_2(sK4(X4),X0,X4)
        & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
            | ~ m1_connsp_2(X3,X0,sK3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK3,X1)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
                  ( ~ r1_tarski(X3,sK2)
                  | ~ m1_connsp_2(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,sK2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK2,X0) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( r1_tarski(X5,sK2)
                  & m1_connsp_2(X5,X0,X4)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,sK2)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v3_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
                    | ~ m1_connsp_2(X3,sK1,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK1)) )
            | ~ v3_pre_topc(X1,sK1) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,sK1,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ( ! [X3] :
            ( ~ r1_tarski(X3,sK2)
            | ~ m1_connsp_2(X3,sK1,sK3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & r2_hidden(sK3,sK2)
        & m1_subset_1(sK3,u1_struct_0(sK1)) )
      | ~ v3_pre_topc(sK2,sK1) )
    & ( ! [X4] :
          ( ( r1_tarski(sK4(X4),sK2)
            & m1_connsp_2(sK4(X4),sK1,X4)
            & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(sK1))) )
          | ~ r2_hidden(X4,sK2)
          | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f46,f50,f49,f48,f47])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ m1_connsp_2(X3,sK1,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,
    ( r2_hidden(sK3,sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    ! [X4] :
      ( m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ! [X4] :
      ( m1_connsp_2(sK4(X4),sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X4] :
      ( r1_tarski(sK4(X4),sK2)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1731,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1723,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_1717,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1732,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3339,plain,
    ( k1_tops_1(sK1,X0) = k1_tops_1(sK1,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_1732])).

cnf(c_12195,plain,
    ( k1_tops_1(sK1,X0) = k1_tops_1(sK1,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_3339])).

cnf(c_95,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1098,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1810,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_2073,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_2074,plain,
    ( X0 != X1
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2073])).

cnf(c_1093,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2517,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_12588,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k1_tops_1(sK1,X0) = k1_tops_1(sK1,X1)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12195,c_95,c_2074,c_2517])).

cnf(c_12589,plain,
    ( k1_tops_1(sK1,X0) = k1_tops_1(sK1,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12588])).

cnf(c_12595,plain,
    ( k1_tops_1(sK1,X0) = k1_tops_1(sK1,sK2)
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_12589])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_1821,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_1822,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1821])).

cnf(c_14,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_528,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_529,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_533,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_529,c_27])).

cnf(c_534,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_533])).

cnf(c_653,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_534])).

cnf(c_654,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_1088,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_654])).

cnf(c_1089,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_654])).

cnf(c_1087,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_654])).

cnf(c_1192,plain,
    ( k1_tops_1(sK1,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1088,c_1089,c_1087])).

cnf(c_1193,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_1192])).

cnf(c_1835,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_1836,plain,
    ( k1_tops_1(sK1,sK2) != sK2
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1835])).

cnf(c_1899,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2))
    | k1_tops_1(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1900,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_1844,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK2),k1_tops_1(sK1,X0))
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_1909,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_2128,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2720,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2721,plain,
    ( X0 = sK2
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2720])).

cnf(c_2566,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(k1_tops_1(sK1,sK2),X0)
    | k1_tops_1(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3438,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK2))
    | k1_tops_1(sK1,sK2) = k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2566])).

cnf(c_20,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK1,sK3)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_413,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_414,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_418,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_28,c_27])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_434,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_418,c_9])).

cnf(c_759,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X2,X0)
    | ~ r1_tarski(X1,sK2)
    | X0 != X1
    | sK3 != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_434])).

cnf(c_760,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,X0)
    | ~ r1_tarski(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_1708,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,X0) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_3525,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1708])).

cnf(c_21,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2129,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_3536,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3525,c_44,c_2129])).

cnf(c_1095,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3394,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK1,sK2),X2)
    | X2 != X1
    | k1_tops_1(sK1,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_5646,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK2),X0)
    | r1_tarski(k1_tops_1(sK1,sK2),X1)
    | X1 != X0
    | k1_tops_1(sK1,sK2) != k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3394])).

cnf(c_9837,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),X0)
    | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | X0 != sK2
    | k1_tops_1(sK1,sK2) != k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_5646])).

cnf(c_9838,plain,
    ( X0 != sK2
    | k1_tops_1(sK1,sK2) != k1_tops_1(sK1,sK2)
    | r1_tarski(k1_tops_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9837])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X0,X2),X0)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X2,X0),X2)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_224])).

cnf(c_946,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_947,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_946])).

cnf(c_997,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_285,c_947])).

cnf(c_1704,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_25,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1724,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_connsp_2(sK4(X0),sK1,X0)
    | v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_442,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_443,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_447,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_28,c_27])).

cnf(c_780,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X2))
    | ~ r2_hidden(X0,sK2)
    | X1 != X0
    | sK4(X0) != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_447])).

cnf(c_781,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_785,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v3_pre_topc(sK2,sK1)
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_25])).

cnf(c_786,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(renaming,[status(thm)],[c_785])).

cnf(c_1707,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_787,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_1728,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3070,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1728])).

cnf(c_4372,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1707,c_44,c_787,c_2129,c_3070,c_3525])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_283,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_224])).

cnf(c_1722,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_4642,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK4(X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4372,c_1722])).

cnf(c_5600,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r1_tarski(sK4(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_4642])).

cnf(c_9659,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,X1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_5600])).

cnf(c_9759,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,X1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9659,c_44,c_2129,c_3070,c_3525])).

cnf(c_9760,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r1_tarski(sK4(X1),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9759])).

cnf(c_9768,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_9760])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2)
    | r1_tarski(sK4(X0),sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1725,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3198,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_1725])).

cnf(c_9782,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9768,c_44,c_2129,c_3198,c_3525])).

cnf(c_9783,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9782])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0,X2),X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_284,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X0)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_224])).

cnf(c_996,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_284,c_947])).

cnf(c_1705,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_9788,plain,
    ( r2_hidden(sK0(X0,X1,k1_tops_1(sK1,sK2)),sK2) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,k1_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9783,c_1705])).

cnf(c_10500,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1704,c_9788])).

cnf(c_12851,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12595,c_26,c_33,c_44,c_1822,c_1836,c_1900,c_1909,c_2128,c_2129,c_2721,c_3438,c_3525,c_9838,c_10500])).

cnf(c_12857,plain,
    ( r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1731,c_12851])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12857,c_2129])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n008.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:55:15 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.84/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/0.97  
% 3.84/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.97  
% 3.84/0.97  ------  iProver source info
% 3.84/0.97  
% 3.84/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.97  git: non_committed_changes: false
% 3.84/0.97  git: last_make_outside_of_git: false
% 3.84/0.97  
% 3.84/0.97  ------ 
% 3.84/0.97  
% 3.84/0.97  ------ Input Options
% 3.84/0.97  
% 3.84/0.97  --out_options                           all
% 3.84/0.97  --tptp_safe_out                         true
% 3.84/0.97  --problem_path                          ""
% 3.84/0.97  --include_path                          ""
% 3.84/0.97  --clausifier                            res/vclausify_rel
% 3.84/0.97  --clausifier_options                    ""
% 3.84/0.97  --stdin                                 false
% 3.84/0.97  --stats_out                             all
% 3.84/0.97  
% 3.84/0.97  ------ General Options
% 3.84/0.97  
% 3.84/0.97  --fof                                   false
% 3.84/0.97  --time_out_real                         305.
% 3.84/0.97  --time_out_virtual                      -1.
% 3.84/0.97  --symbol_type_check                     false
% 3.84/0.97  --clausify_out                          false
% 3.84/0.97  --sig_cnt_out                           false
% 3.84/0.97  --trig_cnt_out                          false
% 3.84/0.97  --trig_cnt_out_tolerance                1.
% 3.84/0.97  --trig_cnt_out_sk_spl                   false
% 3.84/0.97  --abstr_cl_out                          false
% 3.84/0.97  
% 3.84/0.97  ------ Global Options
% 3.84/0.97  
% 3.84/0.97  --schedule                              default
% 3.84/0.97  --add_important_lit                     false
% 3.84/0.97  --prop_solver_per_cl                    1000
% 3.84/0.97  --min_unsat_core                        false
% 3.84/0.97  --soft_assumptions                      false
% 3.84/0.97  --soft_lemma_size                       3
% 3.84/0.97  --prop_impl_unit_size                   0
% 3.84/0.97  --prop_impl_unit                        []
% 3.84/0.97  --share_sel_clauses                     true
% 3.84/0.97  --reset_solvers                         false
% 3.84/0.97  --bc_imp_inh                            [conj_cone]
% 3.84/0.97  --conj_cone_tolerance                   3.
% 3.84/0.97  --extra_neg_conj                        none
% 3.84/0.97  --large_theory_mode                     true
% 3.84/0.97  --prolific_symb_bound                   200
% 3.84/0.97  --lt_threshold                          2000
% 3.84/0.97  --clause_weak_htbl                      true
% 3.84/0.97  --gc_record_bc_elim                     false
% 3.84/0.97  
% 3.84/0.97  ------ Preprocessing Options
% 3.84/0.97  
% 3.84/0.97  --preprocessing_flag                    true
% 3.84/0.97  --time_out_prep_mult                    0.1
% 3.84/0.97  --splitting_mode                        input
% 3.84/0.97  --splitting_grd                         true
% 3.84/0.97  --splitting_cvd                         false
% 3.84/0.97  --splitting_cvd_svl                     false
% 3.84/0.97  --splitting_nvd                         32
% 3.84/0.97  --sub_typing                            true
% 3.84/0.97  --prep_gs_sim                           true
% 3.84/0.97  --prep_unflatten                        true
% 3.84/0.97  --prep_res_sim                          true
% 3.84/0.97  --prep_upred                            true
% 3.84/0.97  --prep_sem_filter                       exhaustive
% 3.84/0.97  --prep_sem_filter_out                   false
% 3.84/0.97  --pred_elim                             true
% 3.84/0.97  --res_sim_input                         true
% 3.84/0.97  --eq_ax_congr_red                       true
% 3.84/0.97  --pure_diseq_elim                       true
% 3.84/0.97  --brand_transform                       false
% 3.84/0.97  --non_eq_to_eq                          false
% 3.84/0.97  --prep_def_merge                        true
% 3.84/0.97  --prep_def_merge_prop_impl              false
% 3.84/0.97  --prep_def_merge_mbd                    true
% 3.84/0.97  --prep_def_merge_tr_red                 false
% 3.84/0.97  --prep_def_merge_tr_cl                  false
% 3.84/0.97  --smt_preprocessing                     true
% 3.84/0.97  --smt_ac_axioms                         fast
% 3.84/0.97  --preprocessed_out                      false
% 3.84/0.97  --preprocessed_stats                    false
% 3.84/0.97  
% 3.84/0.97  ------ Abstraction refinement Options
% 3.84/0.97  
% 3.84/0.97  --abstr_ref                             []
% 3.84/0.97  --abstr_ref_prep                        false
% 3.84/0.97  --abstr_ref_until_sat                   false
% 3.84/0.97  --abstr_ref_sig_restrict                funpre
% 3.84/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.97  --abstr_ref_under                       []
% 3.84/0.97  
% 3.84/0.97  ------ SAT Options
% 3.84/0.97  
% 3.84/0.97  --sat_mode                              false
% 3.84/0.97  --sat_fm_restart_options                ""
% 3.84/0.97  --sat_gr_def                            false
% 3.84/0.97  --sat_epr_types                         true
% 3.84/0.97  --sat_non_cyclic_types                  false
% 3.84/0.97  --sat_finite_models                     false
% 3.84/0.97  --sat_fm_lemmas                         false
% 3.84/0.97  --sat_fm_prep                           false
% 3.84/0.97  --sat_fm_uc_incr                        true
% 3.84/0.97  --sat_out_model                         small
% 3.84/0.97  --sat_out_clauses                       false
% 3.84/0.97  
% 3.84/0.97  ------ QBF Options
% 3.84/0.97  
% 3.84/0.97  --qbf_mode                              false
% 3.84/0.97  --qbf_elim_univ                         false
% 3.84/0.97  --qbf_dom_inst                          none
% 3.84/0.97  --qbf_dom_pre_inst                      false
% 3.84/0.97  --qbf_sk_in                             false
% 3.84/0.97  --qbf_pred_elim                         true
% 3.84/0.97  --qbf_split                             512
% 3.84/0.97  
% 3.84/0.97  ------ BMC1 Options
% 3.84/0.97  
% 3.84/0.97  --bmc1_incremental                      false
% 3.84/0.97  --bmc1_axioms                           reachable_all
% 3.84/0.97  --bmc1_min_bound                        0
% 3.84/0.97  --bmc1_max_bound                        -1
% 3.84/0.97  --bmc1_max_bound_default                -1
% 3.84/0.97  --bmc1_symbol_reachability              true
% 3.84/0.97  --bmc1_property_lemmas                  false
% 3.84/0.97  --bmc1_k_induction                      false
% 3.84/0.97  --bmc1_non_equiv_states                 false
% 3.84/0.97  --bmc1_deadlock                         false
% 3.84/0.97  --bmc1_ucm                              false
% 3.84/0.97  --bmc1_add_unsat_core                   none
% 3.84/0.97  --bmc1_unsat_core_children              false
% 3.84/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.97  --bmc1_out_stat                         full
% 3.84/0.97  --bmc1_ground_init                      false
% 3.84/0.97  --bmc1_pre_inst_next_state              false
% 3.84/0.97  --bmc1_pre_inst_state                   false
% 3.84/0.97  --bmc1_pre_inst_reach_state             false
% 3.84/0.97  --bmc1_out_unsat_core                   false
% 3.84/0.97  --bmc1_aig_witness_out                  false
% 3.84/0.97  --bmc1_verbose                          false
% 3.84/0.97  --bmc1_dump_clauses_tptp                false
% 3.84/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.97  --bmc1_dump_file                        -
% 3.84/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.97  --bmc1_ucm_extend_mode                  1
% 3.84/0.97  --bmc1_ucm_init_mode                    2
% 3.84/0.97  --bmc1_ucm_cone_mode                    none
% 3.84/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.97  --bmc1_ucm_relax_model                  4
% 3.84/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.97  --bmc1_ucm_layered_model                none
% 3.84/0.97  --bmc1_ucm_max_lemma_size               10
% 3.84/0.97  
% 3.84/0.97  ------ AIG Options
% 3.84/0.97  
% 3.84/0.97  --aig_mode                              false
% 3.84/0.97  
% 3.84/0.97  ------ Instantiation Options
% 3.84/0.97  
% 3.84/0.97  --instantiation_flag                    true
% 3.84/0.97  --inst_sos_flag                         true
% 3.84/0.97  --inst_sos_phase                        true
% 3.84/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.97  --inst_lit_sel_side                     num_symb
% 3.84/0.97  --inst_solver_per_active                1400
% 3.84/0.97  --inst_solver_calls_frac                1.
% 3.84/0.97  --inst_passive_queue_type               priority_queues
% 3.84/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.97  --inst_passive_queues_freq              [25;2]
% 3.84/0.97  --inst_dismatching                      true
% 3.84/0.97  --inst_eager_unprocessed_to_passive     true
% 3.84/0.97  --inst_prop_sim_given                   true
% 3.84/0.97  --inst_prop_sim_new                     false
% 3.84/0.97  --inst_subs_new                         false
% 3.84/0.97  --inst_eq_res_simp                      false
% 3.84/0.97  --inst_subs_given                       false
% 3.84/0.97  --inst_orphan_elimination               true
% 3.84/0.97  --inst_learning_loop_flag               true
% 3.84/0.97  --inst_learning_start                   3000
% 3.84/0.97  --inst_learning_factor                  2
% 3.84/0.97  --inst_start_prop_sim_after_learn       3
% 3.84/0.97  --inst_sel_renew                        solver
% 3.84/0.97  --inst_lit_activity_flag                true
% 3.84/0.97  --inst_restr_to_given                   false
% 3.84/0.97  --inst_activity_threshold               500
% 3.84/0.97  --inst_out_proof                        true
% 3.84/0.97  
% 3.84/0.97  ------ Resolution Options
% 3.84/0.97  
% 3.84/0.97  --resolution_flag                       true
% 3.84/0.97  --res_lit_sel                           adaptive
% 3.84/0.97  --res_lit_sel_side                      none
% 3.84/0.97  --res_ordering                          kbo
% 3.84/0.97  --res_to_prop_solver                    active
% 3.84/0.97  --res_prop_simpl_new                    false
% 3.84/0.97  --res_prop_simpl_given                  true
% 3.84/0.97  --res_passive_queue_type                priority_queues
% 3.84/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.97  --res_passive_queues_freq               [15;5]
% 3.84/0.97  --res_forward_subs                      full
% 3.84/0.97  --res_backward_subs                     full
% 3.84/0.97  --res_forward_subs_resolution           true
% 3.84/0.97  --res_backward_subs_resolution          true
% 3.84/0.97  --res_orphan_elimination                true
% 3.84/0.97  --res_time_limit                        2.
% 3.84/0.97  --res_out_proof                         true
% 3.84/0.97  
% 3.84/0.97  ------ Superposition Options
% 3.84/0.97  
% 3.84/0.97  --superposition_flag                    true
% 3.84/0.97  --sup_passive_queue_type                priority_queues
% 3.84/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.97  --demod_completeness_check              fast
% 3.84/0.97  --demod_use_ground                      true
% 3.84/0.97  --sup_to_prop_solver                    passive
% 3.84/0.97  --sup_prop_simpl_new                    true
% 3.84/0.97  --sup_prop_simpl_given                  true
% 3.84/0.97  --sup_fun_splitting                     true
% 3.84/0.97  --sup_smt_interval                      50000
% 3.84/0.97  
% 3.84/0.97  ------ Superposition Simplification Setup
% 3.84/0.97  
% 3.84/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/0.97  --sup_immed_triv                        [TrivRules]
% 3.84/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.97  --sup_immed_bw_main                     []
% 3.84/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.97  --sup_input_bw                          []
% 3.84/0.97  
% 3.84/0.97  ------ Combination Options
% 3.84/0.97  
% 3.84/0.97  --comb_res_mult                         3
% 3.84/0.97  --comb_sup_mult                         2
% 3.84/0.97  --comb_inst_mult                        10
% 3.84/0.97  
% 3.84/0.97  ------ Debug Options
% 3.84/0.97  
% 3.84/0.97  --dbg_backtrace                         false
% 3.84/0.97  --dbg_dump_prop_clauses                 false
% 3.84/0.97  --dbg_dump_prop_clauses_file            -
% 3.84/0.97  --dbg_out_stat                          false
% 3.84/0.97  ------ Parsing...
% 3.84/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.97  
% 3.84/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.84/0.97  
% 3.84/0.97  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.97  
% 3.84/0.97  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/0.97  ------ Proving...
% 3.84/0.97  ------ Problem Properties 
% 3.84/0.97  
% 3.84/0.97  
% 3.84/0.97  clauses                                 30
% 3.84/0.97  conjectures                             5
% 3.84/0.97  EPR                                     6
% 3.84/0.97  Horn                                    22
% 3.84/0.97  unary                                   2
% 3.84/0.97  binary                                  11
% 3.84/0.97  lits                                    90
% 3.84/0.97  lits eq                                 3
% 3.84/0.97  fd_pure                                 0
% 3.84/0.97  fd_pseudo                               0
% 3.84/0.97  fd_cond                                 0
% 3.84/0.97  fd_pseudo_cond                          1
% 3.84/0.97  AC symbols                              0
% 3.84/0.97  
% 3.84/0.97  ------ Schedule dynamic 5 is on 
% 3.84/0.97  
% 3.84/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/0.97  
% 3.84/0.97  
% 3.84/0.97  ------ 
% 3.84/0.97  Current options:
% 3.84/0.97  ------ 
% 3.84/0.97  
% 3.84/0.97  ------ Input Options
% 3.84/0.97  
% 3.84/0.97  --out_options                           all
% 3.84/0.97  --tptp_safe_out                         true
% 3.84/0.97  --problem_path                          ""
% 3.84/0.97  --include_path                          ""
% 3.84/0.97  --clausifier                            res/vclausify_rel
% 3.84/0.97  --clausifier_options                    ""
% 3.84/0.97  --stdin                                 false
% 3.84/0.97  --stats_out                             all
% 3.84/0.97  
% 3.84/0.97  ------ General Options
% 3.84/0.97  
% 3.84/0.97  --fof                                   false
% 3.84/0.97  --time_out_real                         305.
% 3.84/0.97  --time_out_virtual                      -1.
% 3.84/0.97  --symbol_type_check                     false
% 3.84/0.97  --clausify_out                          false
% 3.84/0.97  --sig_cnt_out                           false
% 3.84/0.97  --trig_cnt_out                          false
% 3.84/0.97  --trig_cnt_out_tolerance                1.
% 3.84/0.97  --trig_cnt_out_sk_spl                   false
% 3.84/0.97  --abstr_cl_out                          false
% 3.84/0.97  
% 3.84/0.97  ------ Global Options
% 3.84/0.97  
% 3.84/0.97  --schedule                              default
% 3.84/0.97  --add_important_lit                     false
% 3.84/0.97  --prop_solver_per_cl                    1000
% 3.84/0.97  --min_unsat_core                        false
% 3.84/0.97  --soft_assumptions                      false
% 3.84/0.97  --soft_lemma_size                       3
% 3.84/0.97  --prop_impl_unit_size                   0
% 3.84/0.97  --prop_impl_unit                        []
% 3.84/0.97  --share_sel_clauses                     true
% 3.84/0.97  --reset_solvers                         false
% 3.84/0.97  --bc_imp_inh                            [conj_cone]
% 3.84/0.97  --conj_cone_tolerance                   3.
% 3.84/0.97  --extra_neg_conj                        none
% 3.84/0.97  --large_theory_mode                     true
% 3.84/0.97  --prolific_symb_bound                   200
% 3.84/0.97  --lt_threshold                          2000
% 3.84/0.97  --clause_weak_htbl                      true
% 3.84/0.97  --gc_record_bc_elim                     false
% 3.84/0.97  
% 3.84/0.97  ------ Preprocessing Options
% 3.84/0.97  
% 3.84/0.97  --preprocessing_flag                    true
% 3.84/0.97  --time_out_prep_mult                    0.1
% 3.84/0.97  --splitting_mode                        input
% 3.84/0.97  --splitting_grd                         true
% 3.84/0.97  --splitting_cvd                         false
% 3.84/0.97  --splitting_cvd_svl                     false
% 3.84/0.97  --splitting_nvd                         32
% 3.84/0.97  --sub_typing                            true
% 3.84/0.97  --prep_gs_sim                           true
% 3.84/0.97  --prep_unflatten                        true
% 3.84/0.97  --prep_res_sim                          true
% 3.84/0.97  --prep_upred                            true
% 3.84/0.97  --prep_sem_filter                       exhaustive
% 3.84/0.97  --prep_sem_filter_out                   false
% 3.84/0.97  --pred_elim                             true
% 3.84/0.97  --res_sim_input                         true
% 3.84/0.97  --eq_ax_congr_red                       true
% 3.84/0.97  --pure_diseq_elim                       true
% 3.84/0.97  --brand_transform                       false
% 3.84/0.97  --non_eq_to_eq                          false
% 3.84/0.97  --prep_def_merge                        true
% 3.84/0.97  --prep_def_merge_prop_impl              false
% 3.84/0.97  --prep_def_merge_mbd                    true
% 3.84/0.97  --prep_def_merge_tr_red                 false
% 3.84/0.97  --prep_def_merge_tr_cl                  false
% 3.84/0.97  --smt_preprocessing                     true
% 3.84/0.97  --smt_ac_axioms                         fast
% 3.84/0.97  --preprocessed_out                      false
% 3.84/0.97  --preprocessed_stats                    false
% 3.84/0.97  
% 3.84/0.97  ------ Abstraction refinement Options
% 3.84/0.97  
% 3.84/0.97  --abstr_ref                             []
% 3.84/0.97  --abstr_ref_prep                        false
% 3.84/0.97  --abstr_ref_until_sat                   false
% 3.84/0.97  --abstr_ref_sig_restrict                funpre
% 3.84/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.97  --abstr_ref_under                       []
% 3.84/0.97  
% 3.84/0.97  ------ SAT Options
% 3.84/0.97  
% 3.84/0.97  --sat_mode                              false
% 3.84/0.97  --sat_fm_restart_options                ""
% 3.84/0.97  --sat_gr_def                            false
% 3.84/0.97  --sat_epr_types                         true
% 3.84/0.97  --sat_non_cyclic_types                  false
% 3.84/0.97  --sat_finite_models                     false
% 3.84/0.97  --sat_fm_lemmas                         false
% 3.84/0.97  --sat_fm_prep                           false
% 3.84/0.97  --sat_fm_uc_incr                        true
% 3.84/0.97  --sat_out_model                         small
% 3.84/0.97  --sat_out_clauses                       false
% 3.84/0.97  
% 3.84/0.97  ------ QBF Options
% 3.84/0.97  
% 3.84/0.97  --qbf_mode                              false
% 3.84/0.97  --qbf_elim_univ                         false
% 3.84/0.97  --qbf_dom_inst                          none
% 3.84/0.97  --qbf_dom_pre_inst                      false
% 3.84/0.97  --qbf_sk_in                             false
% 3.84/0.97  --qbf_pred_elim                         true
% 3.84/0.97  --qbf_split                             512
% 3.84/0.97  
% 3.84/0.97  ------ BMC1 Options
% 3.84/0.97  
% 3.84/0.97  --bmc1_incremental                      false
% 3.84/0.97  --bmc1_axioms                           reachable_all
% 3.84/0.97  --bmc1_min_bound                        0
% 3.84/0.97  --bmc1_max_bound                        -1
% 3.84/0.97  --bmc1_max_bound_default                -1
% 3.84/0.97  --bmc1_symbol_reachability              true
% 3.84/0.97  --bmc1_property_lemmas                  false
% 3.84/0.97  --bmc1_k_induction                      false
% 3.84/0.97  --bmc1_non_equiv_states                 false
% 3.84/0.97  --bmc1_deadlock                         false
% 3.84/0.97  --bmc1_ucm                              false
% 3.84/0.97  --bmc1_add_unsat_core                   none
% 3.84/0.97  --bmc1_unsat_core_children              false
% 3.84/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.97  --bmc1_out_stat                         full
% 3.84/0.97  --bmc1_ground_init                      false
% 3.84/0.97  --bmc1_pre_inst_next_state              false
% 3.84/0.97  --bmc1_pre_inst_state                   false
% 3.84/0.97  --bmc1_pre_inst_reach_state             false
% 3.84/0.97  --bmc1_out_unsat_core                   false
% 3.84/0.97  --bmc1_aig_witness_out                  false
% 3.84/0.97  --bmc1_verbose                          false
% 3.84/0.97  --bmc1_dump_clauses_tptp                false
% 3.84/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.97  --bmc1_dump_file                        -
% 3.84/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.97  --bmc1_ucm_extend_mode                  1
% 3.84/0.97  --bmc1_ucm_init_mode                    2
% 3.84/0.97  --bmc1_ucm_cone_mode                    none
% 3.84/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.97  --bmc1_ucm_relax_model                  4
% 3.84/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.97  --bmc1_ucm_layered_model                none
% 3.84/0.97  --bmc1_ucm_max_lemma_size               10
% 3.84/0.97  
% 3.84/0.97  ------ AIG Options
% 3.84/0.97  
% 3.84/0.97  --aig_mode                              false
% 3.84/0.97  
% 3.84/0.97  ------ Instantiation Options
% 3.84/0.97  
% 3.84/0.97  --instantiation_flag                    true
% 3.84/0.97  --inst_sos_flag                         true
% 3.84/0.97  --inst_sos_phase                        true
% 3.84/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.97  --inst_lit_sel_side                     none
% 3.84/0.97  --inst_solver_per_active                1400
% 3.84/0.97  --inst_solver_calls_frac                1.
% 3.84/0.97  --inst_passive_queue_type               priority_queues
% 3.84/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.97  --inst_passive_queues_freq              [25;2]
% 3.84/0.97  --inst_dismatching                      true
% 3.84/0.97  --inst_eager_unprocessed_to_passive     true
% 3.84/0.97  --inst_prop_sim_given                   true
% 3.84/0.97  --inst_prop_sim_new                     false
% 3.84/0.97  --inst_subs_new                         false
% 3.84/0.97  --inst_eq_res_simp                      false
% 3.84/0.97  --inst_subs_given                       false
% 3.84/0.97  --inst_orphan_elimination               true
% 3.84/0.97  --inst_learning_loop_flag               true
% 3.84/0.97  --inst_learning_start                   3000
% 3.84/0.97  --inst_learning_factor                  2
% 3.84/0.97  --inst_start_prop_sim_after_learn       3
% 3.84/0.97  --inst_sel_renew                        solver
% 3.84/0.97  --inst_lit_activity_flag                true
% 3.84/0.97  --inst_restr_to_given                   false
% 3.84/0.97  --inst_activity_threshold               500
% 3.84/0.97  --inst_out_proof                        true
% 3.84/0.97  
% 3.84/0.97  ------ Resolution Options
% 3.84/0.97  
% 3.84/0.97  --resolution_flag                       false
% 3.84/0.97  --res_lit_sel                           adaptive
% 3.84/0.97  --res_lit_sel_side                      none
% 3.84/0.97  --res_ordering                          kbo
% 3.84/0.97  --res_to_prop_solver                    active
% 3.84/0.97  --res_prop_simpl_new                    false
% 3.84/0.97  --res_prop_simpl_given                  true
% 3.84/0.97  --res_passive_queue_type                priority_queues
% 3.84/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.97  --res_passive_queues_freq               [15;5]
% 3.84/0.97  --res_forward_subs                      full
% 3.84/0.97  --res_backward_subs                     full
% 3.84/0.97  --res_forward_subs_resolution           true
% 3.84/0.97  --res_backward_subs_resolution          true
% 3.84/0.97  --res_orphan_elimination                true
% 3.84/0.97  --res_time_limit                        2.
% 3.84/0.97  --res_out_proof                         true
% 3.84/0.97  
% 3.84/0.97  ------ Superposition Options
% 3.84/0.97  
% 3.84/0.97  --superposition_flag                    true
% 3.84/0.97  --sup_passive_queue_type                priority_queues
% 3.84/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.97  --demod_completeness_check              fast
% 3.84/0.97  --demod_use_ground                      true
% 3.84/0.97  --sup_to_prop_solver                    passive
% 3.84/0.97  --sup_prop_simpl_new                    true
% 3.84/0.97  --sup_prop_simpl_given                  true
% 3.84/0.97  --sup_fun_splitting                     true
% 3.84/0.97  --sup_smt_interval                      50000
% 3.84/0.97  
% 3.84/0.97  ------ Superposition Simplification Setup
% 3.84/0.97  
% 3.84/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/0.97  --sup_immed_triv                        [TrivRules]
% 3.84/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.97  --sup_immed_bw_main                     []
% 3.84/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.97  --sup_input_bw                          []
% 3.84/0.97  
% 3.84/0.97  ------ Combination Options
% 3.84/0.97  
% 3.84/0.97  --comb_res_mult                         3
% 3.84/0.97  --comb_sup_mult                         2
% 3.84/0.97  --comb_inst_mult                        10
% 3.84/0.97  
% 3.84/0.97  ------ Debug Options
% 3.84/0.97  
% 3.84/0.97  --dbg_backtrace                         false
% 3.84/0.97  --dbg_dump_prop_clauses                 false
% 3.84/0.97  --dbg_dump_prop_clauses_file            -
% 3.84/0.97  --dbg_out_stat                          false
% 3.84/0.97  
% 3.84/0.97  
% 3.84/0.97  
% 3.84/0.97  
% 3.84/0.97  ------ Proving...
% 3.84/0.97  
% 3.84/0.97  
% 3.84/0.97  % SZS status Theorem for theBenchmark.p
% 3.84/0.97  
% 3.84/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.97  
% 3.84/0.97  fof(f1,axiom,(
% 3.84/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f38,plain,(
% 3.84/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/0.97    inference(nnf_transformation,[],[f1])).
% 3.84/0.97  
% 3.84/0.97  fof(f39,plain,(
% 3.84/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/0.97    inference(flattening,[],[f38])).
% 3.84/0.97  
% 3.84/0.97  fof(f52,plain,(
% 3.84/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.84/0.97    inference(cnf_transformation,[],[f39])).
% 3.84/0.97  
% 3.84/0.97  fof(f83,plain,(
% 3.84/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/0.97    inference(equality_resolution,[],[f52])).
% 3.84/0.97  
% 3.84/0.97  fof(f14,conjecture,(
% 3.84/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f15,negated_conjecture,(
% 3.84/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.84/0.97    inference(negated_conjecture,[],[f14])).
% 3.84/0.97  
% 3.84/0.97  fof(f36,plain,(
% 3.84/0.97    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.84/0.97    inference(ennf_transformation,[],[f15])).
% 3.84/0.97  
% 3.84/0.97  fof(f37,plain,(
% 3.84/0.97    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.84/0.97    inference(flattening,[],[f36])).
% 3.84/0.97  
% 3.84/0.97  fof(f44,plain,(
% 3.84/0.97    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.84/0.97    inference(nnf_transformation,[],[f37])).
% 3.84/0.97  
% 3.84/0.97  fof(f45,plain,(
% 3.84/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.84/0.97    inference(flattening,[],[f44])).
% 3.84/0.97  
% 3.84/0.97  fof(f46,plain,(
% 3.84/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.84/0.97    inference(rectify,[],[f45])).
% 3.84/0.97  
% 3.84/0.97  fof(f50,plain,(
% 3.84/0.97    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK4(X4),X1) & m1_connsp_2(sK4(X4),X0,X4) & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.84/0.97    introduced(choice_axiom,[])).
% 3.84/0.97  
% 3.84/0.97  fof(f49,plain,(
% 3.84/0.97    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK3,X1) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.84/0.97    introduced(choice_axiom,[])).
% 3.84/0.97  
% 3.84/0.97  fof(f48,plain,(
% 3.84/0.97    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK2,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK2) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.84/0.97    introduced(choice_axiom,[])).
% 3.84/0.97  
% 3.84/0.97  fof(f47,plain,(
% 3.84/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK1,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.84/0.97    introduced(choice_axiom,[])).
% 3.84/0.97  
% 3.84/0.97  fof(f51,plain,(
% 3.84/0.97    (((! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,sK1,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & r2_hidden(sK3,sK2) & m1_subset_1(sK3,u1_struct_0(sK1))) | ~v3_pre_topc(sK2,sK1)) & (! [X4] : ((r1_tarski(sK4(X4),sK2) & m1_connsp_2(sK4(X4),sK1,X4) & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.84/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f46,f50,f49,f48,f47])).
% 3.84/0.97  
% 3.84/0.97  fof(f75,plain,(
% 3.84/0.97    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f9,axiom,(
% 3.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f26,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.97    inference(ennf_transformation,[],[f9])).
% 3.84/0.97  
% 3.84/0.97  fof(f27,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.97    inference(flattening,[],[f26])).
% 3.84/0.97  
% 3.84/0.97  fof(f65,plain,(
% 3.84/0.97    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f27])).
% 3.84/0.97  
% 3.84/0.97  fof(f74,plain,(
% 3.84/0.97    l1_pre_topc(sK1)),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f54,plain,(
% 3.84/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f39])).
% 3.84/0.97  
% 3.84/0.97  fof(f8,axiom,(
% 3.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f25,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.97    inference(ennf_transformation,[],[f8])).
% 3.84/0.97  
% 3.84/0.97  fof(f64,plain,(
% 3.84/0.97    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f25])).
% 3.84/0.97  
% 3.84/0.97  fof(f10,axiom,(
% 3.84/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f28,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.97    inference(ennf_transformation,[],[f10])).
% 3.84/0.97  
% 3.84/0.97  fof(f29,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.97    inference(flattening,[],[f28])).
% 3.84/0.97  
% 3.84/0.97  fof(f67,plain,(
% 3.84/0.97    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f29])).
% 3.84/0.97  
% 3.84/0.97  fof(f73,plain,(
% 3.84/0.97    v2_pre_topc(sK1)),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f81,plain,(
% 3.84/0.97    ( ! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,sK1,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(sK2,sK1)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f12,axiom,(
% 3.84/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f32,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.84/0.97    inference(ennf_transformation,[],[f12])).
% 3.84/0.97  
% 3.84/0.97  fof(f33,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.84/0.97    inference(flattening,[],[f32])).
% 3.84/0.97  
% 3.84/0.97  fof(f70,plain,(
% 3.84/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f33])).
% 3.84/0.97  
% 3.84/0.97  fof(f72,plain,(
% 3.84/0.97    ~v2_struct_0(sK1)),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f5,axiom,(
% 3.84/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f19,plain,(
% 3.84/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.84/0.97    inference(ennf_transformation,[],[f5])).
% 3.84/0.97  
% 3.84/0.97  fof(f20,plain,(
% 3.84/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.84/0.97    inference(flattening,[],[f19])).
% 3.84/0.97  
% 3.84/0.97  fof(f61,plain,(
% 3.84/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f20])).
% 3.84/0.97  
% 3.84/0.97  fof(f80,plain,(
% 3.84/0.97    r2_hidden(sK3,sK2) | ~v3_pre_topc(sK2,sK1)),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f3,axiom,(
% 3.84/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f17,plain,(
% 3.84/0.97    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.97    inference(ennf_transformation,[],[f3])).
% 3.84/0.97  
% 3.84/0.97  fof(f18,plain,(
% 3.84/0.97    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.97    inference(flattening,[],[f17])).
% 3.84/0.97  
% 3.84/0.97  fof(f40,plain,(
% 3.84/0.97    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.84/0.97    introduced(choice_axiom,[])).
% 3.84/0.97  
% 3.84/0.97  fof(f41,plain,(
% 3.84/0.97    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f40])).
% 3.84/0.97  
% 3.84/0.97  fof(f57,plain,(
% 3.84/0.97    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.97    inference(cnf_transformation,[],[f41])).
% 3.84/0.97  
% 3.84/0.97  fof(f4,axiom,(
% 3.84/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f42,plain,(
% 3.84/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.84/0.97    inference(nnf_transformation,[],[f4])).
% 3.84/0.97  
% 3.84/0.97  fof(f60,plain,(
% 3.84/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f42])).
% 3.84/0.97  
% 3.84/0.97  fof(f76,plain,(
% 3.84/0.97    ( ! [X4] : (m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v3_pre_topc(sK2,sK1)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f77,plain,(
% 3.84/0.97    ( ! [X4] : (m1_connsp_2(sK4(X4),sK1,X4) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v3_pre_topc(sK2,sK1)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f11,axiom,(
% 3.84/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f30,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.84/0.97    inference(ennf_transformation,[],[f11])).
% 3.84/0.97  
% 3.84/0.97  fof(f31,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.84/0.97    inference(flattening,[],[f30])).
% 3.84/0.97  
% 3.84/0.97  fof(f43,plain,(
% 3.84/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.84/0.97    inference(nnf_transformation,[],[f31])).
% 3.84/0.97  
% 3.84/0.97  fof(f68,plain,(
% 3.84/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f43])).
% 3.84/0.97  
% 3.84/0.97  fof(f2,axiom,(
% 3.84/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.97  
% 3.84/0.97  fof(f16,plain,(
% 3.84/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.97    inference(ennf_transformation,[],[f2])).
% 3.84/0.97  
% 3.84/0.97  fof(f55,plain,(
% 3.84/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.97    inference(cnf_transformation,[],[f16])).
% 3.84/0.97  
% 3.84/0.97  fof(f78,plain,(
% 3.84/0.97    ( ! [X4] : (r1_tarski(sK4(X4),sK2) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v3_pre_topc(sK2,sK1)) )),
% 3.84/0.97    inference(cnf_transformation,[],[f51])).
% 3.84/0.97  
% 3.84/0.97  fof(f58,plain,(
% 3.84/0.97    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.97    inference(cnf_transformation,[],[f41])).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2,plain,
% 3.84/0.97      ( r1_tarski(X0,X0) ),
% 3.84/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1731,plain,
% 3.84/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_26,negated_conjecture,
% 3.84/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.84/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1723,plain,
% 3.84/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_13,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | ~ r1_tarski(X0,X2)
% 3.84/0.97      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.84/0.97      | ~ l1_pre_topc(X1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_27,negated_conjecture,
% 3.84/0.97      ( l1_pre_topc(sK1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_611,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | ~ r1_tarski(X0,X2)
% 3.84/0.97      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.84/0.97      | sK1 != X1 ),
% 3.84/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_612,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ r1_tarski(X0,X1)
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
% 3.84/0.97      inference(unflattening,[status(thm)],[c_611]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1717,plain,
% 3.84/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_0,plain,
% 3.84/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.84/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1732,plain,
% 3.84/0.97      ( X0 = X1
% 3.84/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_3339,plain,
% 3.84/0.97      ( k1_tops_1(sK1,X0) = k1_tops_1(sK1,X1)
% 3.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1717,c_1732]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_12195,plain,
% 3.84/0.97      ( k1_tops_1(sK1,X0) = k1_tops_1(sK1,X1)
% 3.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1717,c_3339]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_95,plain,
% 3.84/0.97      ( X0 = X1
% 3.84/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1098,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.84/0.97      theory(equality) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1810,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,X1)
% 3.84/0.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | X2 != X0
% 3.84/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_1098]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2073,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | X1 != X0
% 3.84/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_1810]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2074,plain,
% 3.84/0.97      ( X0 != X1
% 3.84/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 3.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_2073]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1093,plain,( X0 = X0 ),theory(equality) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2517,plain,
% 3.84/0.97      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_1093]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_12588,plain,
% 3.84/0.97      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | k1_tops_1(sK1,X0) = k1_tops_1(sK1,X1)
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_12195,c_95,c_2074,c_2517]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_12589,plain,
% 3.84/0.97      ( k1_tops_1(sK1,X0) = k1_tops_1(sK1,X1)
% 3.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 3.84/0.97      inference(renaming,[status(thm)],[c_12588]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_12595,plain,
% 3.84/0.97      ( k1_tops_1(sK1,X0) = k1_tops_1(sK1,sK2)
% 3.84/0.97      | r1_tarski(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1723,c_12589]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_33,plain,
% 3.84/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_12,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.84/0.97      | ~ l1_pre_topc(X1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_629,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.84/0.97      | sK1 != X1 ),
% 3.84/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_630,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 3.84/0.97      inference(unflattening,[status(thm)],[c_629]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1821,plain,
% 3.84/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_630]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1822,plain,
% 3.84/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_1821]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_14,plain,
% 3.84/0.97      ( v3_pre_topc(X0,X1)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.84/0.97      | ~ v2_pre_topc(X1)
% 3.84/0.97      | ~ l1_pre_topc(X1)
% 3.84/0.97      | ~ l1_pre_topc(X3)
% 3.84/0.97      | k1_tops_1(X1,X0) != X0 ),
% 3.84/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_28,negated_conjecture,
% 3.84/0.97      ( v2_pre_topc(sK1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_528,plain,
% 3.84/0.97      ( v3_pre_topc(X0,X1)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.84/0.97      | ~ l1_pre_topc(X1)
% 3.84/0.97      | ~ l1_pre_topc(X3)
% 3.84/0.97      | k1_tops_1(X1,X0) != X0
% 3.84/0.97      | sK1 != X1 ),
% 3.84/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_529,plain,
% 3.84/0.97      ( v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ l1_pre_topc(X2)
% 3.84/0.97      | ~ l1_pre_topc(sK1)
% 3.84/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 3.84/0.97      inference(unflattening,[status(thm)],[c_528]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_533,plain,
% 3.84/0.97      ( ~ l1_pre_topc(X2)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.84/0.97      | v3_pre_topc(X0,sK1)
% 3.84/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_529,c_27]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_534,plain,
% 3.84/0.97      ( v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ l1_pre_topc(X2)
% 3.84/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 3.84/0.97      inference(renaming,[status(thm)],[c_533]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_653,plain,
% 3.84/0.97      ( v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | k1_tops_1(sK1,X0) != X0
% 3.84/0.97      | sK1 != X2 ),
% 3.84/0.97      inference(resolution_lifted,[status(thm)],[c_27,c_534]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_654,plain,
% 3.84/0.97      ( v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 3.84/0.97      inference(unflattening,[status(thm)],[c_653]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1088,plain,
% 3.84/0.97      ( v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | k1_tops_1(sK1,X0) != X0
% 3.84/0.97      | ~ sP1_iProver_split ),
% 3.84/0.97      inference(splitting,
% 3.84/0.97                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.84/0.97                [c_654]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1089,plain,
% 3.84/0.97      ( sP1_iProver_split | sP0_iProver_split ),
% 3.84/0.97      inference(splitting,
% 3.84/0.97                [splitting(split),new_symbols(definition,[])],
% 3.84/0.97                [c_654]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1087,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ sP0_iProver_split ),
% 3.84/0.97      inference(splitting,
% 3.84/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.84/0.97                [c_654]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1192,plain,
% 3.84/0.97      ( k1_tops_1(sK1,X0) != X0
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | v3_pre_topc(X0,sK1) ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_1088,c_1089,c_1087]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1193,plain,
% 3.84/0.97      ( v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 3.84/0.97      inference(renaming,[status(thm)],[c_1192]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1835,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | k1_tops_1(sK1,sK2) != sK2 ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_1193]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1836,plain,
% 3.84/0.97      ( k1_tops_1(sK1,sK2) != sK2
% 3.84/0.97      | v3_pre_topc(sK2,sK1) = iProver_top
% 3.84/0.97      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_1835]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1899,plain,
% 3.84/0.97      ( ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
% 3.84/0.97      | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2))
% 3.84/0.97      | k1_tops_1(sK1,sK2) = sK2 ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1900,plain,
% 3.84/0.97      ( k1_tops_1(sK1,sK2) = sK2
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK2,k1_tops_1(sK1,sK2)) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1844,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),k1_tops_1(sK1,X0))
% 3.84/0.97      | ~ r1_tarski(sK2,X0) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_612]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1909,plain,
% 3.84/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK2))
% 3.84/0.97      | ~ r1_tarski(sK2,sK2) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_1844]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2128,plain,
% 3.84/0.97      ( r1_tarski(sK2,sK2) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2720,plain,
% 3.84/0.97      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2721,plain,
% 3.84/0.97      ( X0 = sK2
% 3.84/0.97      | r1_tarski(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_2720]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2566,plain,
% 3.84/0.97      ( ~ r1_tarski(X0,k1_tops_1(sK1,sK2))
% 3.84/0.97      | ~ r1_tarski(k1_tops_1(sK1,sK2),X0)
% 3.84/0.97      | k1_tops_1(sK1,sK2) = X0 ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_3438,plain,
% 3.84/0.97      ( ~ r1_tarski(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK2))
% 3.84/0.97      | k1_tops_1(sK1,sK2) = k1_tops_1(sK1,sK2) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_2566]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_20,negated_conjecture,
% 3.84/0.97      ( ~ m1_connsp_2(X0,sK1,sK3)
% 3.84/0.97      | ~ v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ r1_tarski(X0,sK2) ),
% 3.84/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_18,plain,
% 3.84/0.97      ( m1_connsp_2(X0,X1,X2)
% 3.84/0.97      | ~ v3_pre_topc(X0,X1)
% 3.84/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | ~ r2_hidden(X2,X0)
% 3.84/0.97      | v2_struct_0(X1)
% 3.84/0.97      | ~ v2_pre_topc(X1)
% 3.84/0.97      | ~ l1_pre_topc(X1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_29,negated_conjecture,
% 3.84/0.97      ( ~ v2_struct_0(sK1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_413,plain,
% 3.84/0.97      ( m1_connsp_2(X0,X1,X2)
% 3.84/0.97      | ~ v3_pre_topc(X0,X1)
% 3.84/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | ~ r2_hidden(X2,X0)
% 3.84/0.97      | ~ v2_pre_topc(X1)
% 3.84/0.97      | ~ l1_pre_topc(X1)
% 3.84/0.97      | sK1 != X1 ),
% 3.84/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_414,plain,
% 3.84/0.97      ( m1_connsp_2(X0,sK1,X1)
% 3.84/0.97      | ~ v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ r2_hidden(X1,X0)
% 3.84/0.97      | ~ v2_pre_topc(sK1)
% 3.84/0.97      | ~ l1_pre_topc(sK1) ),
% 3.84/0.97      inference(unflattening,[status(thm)],[c_413]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_418,plain,
% 3.84/0.97      ( m1_connsp_2(X0,sK1,X1)
% 3.84/0.97      | ~ v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ r2_hidden(X1,X0) ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_414,c_28,c_27]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9,plain,
% 3.84/0.97      ( m1_subset_1(X0,X1)
% 3.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.84/0.97      | ~ r2_hidden(X0,X2) ),
% 3.84/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_434,plain,
% 3.84/0.97      ( m1_connsp_2(X0,sK1,X1)
% 3.84/0.97      | ~ v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ r2_hidden(X1,X0) ),
% 3.84/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_418,c_9]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_759,plain,
% 3.84/0.97      ( ~ v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ r2_hidden(X2,X0)
% 3.84/0.97      | ~ r1_tarski(X1,sK2)
% 3.84/0.97      | X0 != X1
% 3.84/0.97      | sK3 != X2
% 3.84/0.97      | sK1 != sK1 ),
% 3.84/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_434]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_760,plain,
% 3.84/0.97      ( ~ v3_pre_topc(X0,sK1)
% 3.84/0.97      | ~ v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ r2_hidden(sK3,X0)
% 3.84/0.97      | ~ r1_tarski(X0,sK2) ),
% 3.84/0.97      inference(unflattening,[status(thm)],[c_759]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1708,plain,
% 3.84/0.97      ( v3_pre_topc(X0,sK1) != iProver_top
% 3.84/0.97      | v3_pre_topc(sK2,sK1) != iProver_top
% 3.84/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r2_hidden(sK3,X0) != iProver_top
% 3.84/0.97      | r1_tarski(X0,sK2) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_3525,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) != iProver_top
% 3.84/0.97      | r2_hidden(sK3,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1723,c_1708]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_21,negated_conjecture,
% 3.84/0.97      ( ~ v3_pre_topc(sK2,sK1) | r2_hidden(sK3,sK2) ),
% 3.84/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_44,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) != iProver_top
% 3.84/0.97      | r2_hidden(sK3,sK2) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_2129,plain,
% 3.84/0.97      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_3536,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) != iProver_top ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_3525,c_44,c_2129]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1095,plain,
% 3.84/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.84/0.97      theory(equality) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_3394,plain,
% 3.84/0.97      ( ~ r1_tarski(X0,X1)
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),X2)
% 3.84/0.97      | X2 != X1
% 3.84/0.97      | k1_tops_1(sK1,sK2) != X0 ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_1095]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_5646,plain,
% 3.84/0.97      ( ~ r1_tarski(k1_tops_1(sK1,sK2),X0)
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),X1)
% 3.84/0.97      | X1 != X0
% 3.84/0.97      | k1_tops_1(sK1,sK2) != k1_tops_1(sK1,sK2) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_3394]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9837,plain,
% 3.84/0.97      ( r1_tarski(k1_tops_1(sK1,sK2),X0)
% 3.84/0.97      | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
% 3.84/0.97      | X0 != sK2
% 3.84/0.97      | k1_tops_1(sK1,sK2) != k1_tops_1(sK1,sK2) ),
% 3.84/0.97      inference(instantiation,[status(thm)],[c_5646]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9838,plain,
% 3.84/0.97      ( X0 != sK2
% 3.84/0.97      | k1_tops_1(sK1,sK2) != k1_tops_1(sK1,sK2)
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),X0) = iProver_top
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_9837]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_5,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.84/0.97      | r2_hidden(sK0(X1,X0,X2),X0)
% 3.84/0.97      | r1_tarski(X0,X2) ),
% 3.84/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_7,plain,
% 3.84/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_223,plain,
% 3.84/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.84/0.97      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_224,plain,
% 3.84/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.84/0.97      inference(renaming,[status(thm)],[c_223]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_285,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/0.97      | r2_hidden(sK0(X1,X2,X0),X2)
% 3.84/0.97      | ~ r1_tarski(X2,X1)
% 3.84/0.97      | r1_tarski(X2,X0) ),
% 3.84/0.97      inference(bin_hyper_res,[status(thm)],[c_5,c_224]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_946,plain,
% 3.84/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.84/0.97      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_947,plain,
% 3.84/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.84/0.97      inference(renaming,[status(thm)],[c_946]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_997,plain,
% 3.84/0.97      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.84/0.97      | ~ r1_tarski(X2,X0)
% 3.84/0.97      | ~ r1_tarski(X1,X0)
% 3.84/0.97      | r1_tarski(X1,X2) ),
% 3.84/0.97      inference(bin_hyper_res,[status(thm)],[c_285,c_947]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1704,plain,
% 3.84/0.97      ( r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 3.84/0.97      | r1_tarski(X2,X0) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X2) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_25,negated_conjecture,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.84/0.97      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | ~ r2_hidden(X0,sK2) ),
% 3.84/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1724,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 3.84/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.84/0.97      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_24,negated_conjecture,
% 3.84/0.97      ( m1_connsp_2(sK4(X0),sK1,X0)
% 3.84/0.97      | v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.84/0.97      | ~ r2_hidden(X0,sK2) ),
% 3.84/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_17,plain,
% 3.84/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 3.84/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.84/0.97      | v2_struct_0(X1)
% 3.84/0.97      | ~ v2_pre_topc(X1)
% 3.84/0.97      | ~ l1_pre_topc(X1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_442,plain,
% 3.84/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 3.84/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.84/0.97      | ~ v2_pre_topc(X1)
% 3.84/0.97      | ~ l1_pre_topc(X1)
% 3.84/0.97      | sK1 != X1 ),
% 3.84/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_443,plain,
% 3.84/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.84/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.84/0.97      | ~ v2_pre_topc(sK1)
% 3.84/0.97      | ~ l1_pre_topc(sK1) ),
% 3.84/0.97      inference(unflattening,[status(thm)],[c_442]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_447,plain,
% 3.84/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.84/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_443,c_28,c_27]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_780,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.84/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | r2_hidden(X1,k1_tops_1(sK1,X2))
% 3.84/0.97      | ~ r2_hidden(X0,sK2)
% 3.84/0.97      | X1 != X0
% 3.84/0.97      | sK4(X0) != X2
% 3.84/0.97      | sK1 != sK1 ),
% 3.84/0.97      inference(resolution_lifted,[status(thm)],[c_24,c_447]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_781,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.84/0.97      | ~ m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
% 3.84/0.97      | ~ r2_hidden(X0,sK2) ),
% 3.84/0.97      inference(unflattening,[status(thm)],[c_780]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_785,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.84/0.97      | v3_pre_topc(sK2,sK1)
% 3.84/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
% 3.84/0.97      | ~ r2_hidden(X0,sK2) ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_781,c_25]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_786,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.84/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
% 3.84/0.97      | ~ r2_hidden(X0,sK2) ),
% 3.84/0.97      inference(renaming,[status(thm)],[c_785]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1707,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 3.84/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.84/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_787,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 3.84/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.84/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1728,plain,
% 3.84/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 3.84/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.84/0.97      | r2_hidden(X0,X2) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_3070,plain,
% 3.84/0.97      ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1723,c_1728]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_4372,plain,
% 3.84/0.97      ( r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_1707,c_44,c_787,c_2129,c_3070,c_3525]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_3,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/0.97      | ~ r2_hidden(X2,X0)
% 3.84/0.97      | r2_hidden(X2,X1) ),
% 3.84/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_283,plain,
% 3.84/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.84/0.97      inference(bin_hyper_res,[status(thm)],[c_3,c_224]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1722,plain,
% 3.84/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.84/0.97      | r2_hidden(X0,X2) = iProver_top
% 3.84/0.97      | r1_tarski(X1,X2) != iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_4642,plain,
% 3.84/0.97      ( r2_hidden(X0,X1) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK4(X0)),X1) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_4372,c_1722]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_5600,plain,
% 3.84/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
% 3.84/0.97      | r2_hidden(X1,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK4(X1),X0) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1717,c_4642]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9659,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 3.84/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r2_hidden(X0,k1_tops_1(sK1,X1)) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK4(X0),X1) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1724,c_5600]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9759,plain,
% 3.84/0.97      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r2_hidden(X0,k1_tops_1(sK1,X1)) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK4(X0),X1) != iProver_top ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_9659,c_44,c_2129,c_3070,c_3525]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9760,plain,
% 3.84/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
% 3.84/0.97      | r2_hidden(X1,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK4(X1),X0) != iProver_top ),
% 3.84/0.97      inference(renaming,[status(thm)],[c_9759]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9768,plain,
% 3.84/0.97      ( r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK4(X0),sK2) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1723,c_9760]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_23,negated_conjecture,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1)
% 3.84/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.84/0.97      | ~ r2_hidden(X0,sK2)
% 3.84/0.97      | r1_tarski(sK4(X0),sK2) ),
% 3.84/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1725,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 3.84/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK4(X0),sK2) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_3198,plain,
% 3.84/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK4(X0),sK2) = iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_3070,c_1725]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9782,plain,
% 3.84/0.97      ( r2_hidden(X0,sK2) != iProver_top
% 3.84/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_9768,c_44,c_2129,c_3198,c_3525]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9783,plain,
% 3.84/0.97      ( r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
% 3.84/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 3.84/0.97      inference(renaming,[status(thm)],[c_9782]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_4,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.84/0.97      | ~ r2_hidden(sK0(X1,X0,X2),X2)
% 3.84/0.97      | r1_tarski(X0,X2) ),
% 3.84/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_284,plain,
% 3.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/0.97      | ~ r2_hidden(sK0(X1,X2,X0),X0)
% 3.84/0.97      | ~ r1_tarski(X2,X1)
% 3.84/0.97      | r1_tarski(X2,X0) ),
% 3.84/0.97      inference(bin_hyper_res,[status(thm)],[c_4,c_224]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_996,plain,
% 3.84/0.97      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.84/0.97      | ~ r1_tarski(X2,X0)
% 3.84/0.97      | ~ r1_tarski(X1,X0)
% 3.84/0.97      | r1_tarski(X1,X2) ),
% 3.84/0.97      inference(bin_hyper_res,[status(thm)],[c_284,c_947]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_1705,plain,
% 3.84/0.97      ( r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 3.84/0.97      | r1_tarski(X2,X0) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X2) = iProver_top ),
% 3.84/0.97      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_9788,plain,
% 3.84/0.97      ( r2_hidden(sK0(X0,X1,k1_tops_1(sK1,sK2)),sK2) != iProver_top
% 3.84/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.97      | r1_tarski(X1,k1_tops_1(sK1,sK2)) = iProver_top
% 3.84/0.97      | r1_tarski(k1_tops_1(sK1,sK2),X0) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_9783,c_1705]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_10500,plain,
% 3.84/0.97      ( r1_tarski(k1_tops_1(sK1,sK2),X0) != iProver_top
% 3.84/0.97      | r1_tarski(sK2,X0) != iProver_top
% 3.84/0.97      | r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1704,c_9788]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_12851,plain,
% 3.84/0.97      ( r1_tarski(X0,sK2) != iProver_top
% 3.84/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.84/0.97      inference(global_propositional_subsumption,
% 3.84/0.97                [status(thm)],
% 3.84/0.97                [c_12595,c_26,c_33,c_44,c_1822,c_1836,c_1900,c_1909,
% 3.84/0.97                 c_2128,c_2129,c_2721,c_3438,c_3525,c_9838,c_10500]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(c_12857,plain,
% 3.84/0.97      ( r1_tarski(sK2,sK2) != iProver_top ),
% 3.84/0.97      inference(superposition,[status(thm)],[c_1731,c_12851]) ).
% 3.84/0.97  
% 3.84/0.97  cnf(contradiction,plain,
% 3.84/0.97      ( $false ),
% 3.84/0.97      inference(minisat,[status(thm)],[c_12857,c_2129]) ).
% 3.84/0.97  
% 3.84/0.97  
% 3.84/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/0.97  
% 3.84/0.97  ------                               Statistics
% 3.84/0.97  
% 3.84/0.97  ------ General
% 3.84/0.97  
% 3.84/0.97  abstr_ref_over_cycles:                  0
% 3.84/0.97  abstr_ref_under_cycles:                 0
% 3.84/0.97  gc_basic_clause_elim:                   0
% 3.84/0.97  forced_gc_time:                         0
% 3.84/0.97  parsing_time:                           0.009
% 3.84/0.97  unif_index_cands_time:                  0.
% 3.84/0.97  unif_index_add_time:                    0.
% 3.84/0.97  orderings_time:                         0.
% 3.84/0.97  out_proof_time:                         0.013
% 3.84/0.97  total_time:                             0.372
% 3.84/0.97  num_of_symbols:                         50
% 3.84/0.97  num_of_terms:                           9008
% 3.84/0.97  
% 3.84/0.97  ------ Preprocessing
% 3.84/0.97  
% 3.84/0.97  num_of_splits:                          4
% 3.84/0.97  num_of_split_atoms:                     3
% 3.84/0.97  num_of_reused_defs:                     1
% 3.84/0.97  num_eq_ax_congr_red:                    14
% 3.84/0.97  num_of_sem_filtered_clauses:            4
% 3.84/0.97  num_of_subtypes:                        0
% 3.84/0.97  monotx_restored_types:                  0
% 3.84/0.97  sat_num_of_epr_types:                   0
% 3.84/0.97  sat_num_of_non_cyclic_types:            0
% 3.84/0.97  sat_guarded_non_collapsed_types:        0
% 3.84/0.97  num_pure_diseq_elim:                    0
% 3.84/0.97  simp_replaced_by:                       0
% 3.84/0.97  res_preprocessed:                       129
% 3.84/0.97  prep_upred:                             0
% 3.84/0.97  prep_unflattend:                        22
% 3.84/0.97  smt_new_axioms:                         0
% 3.84/0.97  pred_elim_cands:                        4
% 3.84/0.97  pred_elim:                              4
% 3.84/0.97  pred_elim_cl:                           3
% 3.84/0.97  pred_elim_cycles:                       6
% 3.84/0.97  merged_defs:                            8
% 3.84/0.97  merged_defs_ncl:                        0
% 3.84/0.97  bin_hyper_res:                          15
% 3.84/0.97  prep_cycles:                            4
% 3.84/0.97  pred_elim_time:                         0.014
% 3.84/0.97  splitting_time:                         0.
% 3.84/0.97  sem_filter_time:                        0.
% 3.84/0.97  monotx_time:                            0.001
% 3.84/0.97  subtype_inf_time:                       0.
% 3.84/0.97  
% 3.84/0.97  ------ Problem properties
% 3.84/0.97  
% 3.84/0.97  clauses:                                30
% 3.84/0.97  conjectures:                            5
% 3.84/0.97  epr:                                    6
% 3.84/0.97  horn:                                   22
% 3.84/0.97  ground:                                 5
% 3.84/0.97  unary:                                  2
% 3.84/0.97  binary:                                 11
% 3.84/0.97  lits:                                   90
% 3.84/0.97  lits_eq:                                3
% 3.84/0.97  fd_pure:                                0
% 3.84/0.97  fd_pseudo:                              0
% 3.84/0.97  fd_cond:                                0
% 3.84/0.97  fd_pseudo_cond:                         1
% 3.84/0.97  ac_symbols:                             0
% 3.84/0.97  
% 3.84/0.97  ------ Propositional Solver
% 3.84/0.97  
% 3.84/0.97  prop_solver_calls:                      28
% 3.84/0.97  prop_fast_solver_calls:                 1537
% 3.84/0.97  smt_solver_calls:                       0
% 3.84/0.97  smt_fast_solver_calls:                  0
% 3.84/0.97  prop_num_of_clauses:                    5382
% 3.84/0.97  prop_preprocess_simplified:             13522
% 3.84/0.97  prop_fo_subsumed:                       82
% 3.84/0.97  prop_solver_time:                       0.
% 3.84/0.97  smt_solver_time:                        0.
% 3.84/0.97  smt_fast_solver_time:                   0.
% 3.84/0.97  prop_fast_solver_time:                  0.
% 3.84/0.97  prop_unsat_core_time:                   0.
% 3.84/0.97  
% 3.84/0.97  ------ QBF
% 3.84/0.97  
% 3.84/0.97  qbf_q_res:                              0
% 3.84/0.97  qbf_num_tautologies:                    0
% 3.84/0.97  qbf_prep_cycles:                        0
% 3.84/0.97  
% 3.84/0.97  ------ BMC1
% 3.84/0.97  
% 3.84/0.97  bmc1_current_bound:                     -1
% 3.84/0.97  bmc1_last_solved_bound:                 -1
% 3.84/0.97  bmc1_unsat_core_size:                   -1
% 3.84/0.97  bmc1_unsat_core_parents_size:           -1
% 3.84/0.97  bmc1_merge_next_fun:                    0
% 3.84/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.84/0.97  
% 3.84/0.97  ------ Instantiation
% 3.84/0.97  
% 3.84/0.97  inst_num_of_clauses:                    1601
% 3.84/0.97  inst_num_in_passive:                    696
% 3.84/0.97  inst_num_in_active:                     637
% 3.84/0.97  inst_num_in_unprocessed:                268
% 3.84/0.97  inst_num_of_loops:                      700
% 3.84/0.97  inst_num_of_learning_restarts:          0
% 3.84/0.97  inst_num_moves_active_passive:          62
% 3.84/0.97  inst_lit_activity:                      0
% 3.84/0.97  inst_lit_activity_moves:                0
% 3.84/0.97  inst_num_tautologies:                   0
% 3.84/0.97  inst_num_prop_implied:                  0
% 3.84/0.97  inst_num_existing_simplified:           0
% 3.84/0.97  inst_num_eq_res_simplified:             0
% 3.84/0.97  inst_num_child_elim:                    0
% 3.84/0.97  inst_num_of_dismatching_blockings:      259
% 3.84/0.97  inst_num_of_non_proper_insts:           2023
% 3.84/0.97  inst_num_of_duplicates:                 0
% 3.84/0.97  inst_inst_num_from_inst_to_res:         0
% 3.84/0.97  inst_dismatching_checking_time:         0.
% 3.84/0.97  
% 3.84/0.97  ------ Resolution
% 3.84/0.97  
% 3.84/0.97  res_num_of_clauses:                     0
% 3.84/0.97  res_num_in_passive:                     0
% 3.84/0.97  res_num_in_active:                      0
% 3.84/0.97  res_num_of_loops:                       133
% 3.84/0.97  res_forward_subset_subsumed:            176
% 3.84/0.97  res_backward_subset_subsumed:           0
% 3.84/0.97  res_forward_subsumed:                   0
% 3.84/0.97  res_backward_subsumed:                  0
% 3.84/0.97  res_forward_subsumption_resolution:     2
% 3.84/0.97  res_backward_subsumption_resolution:    0
% 3.84/0.97  res_clause_to_clause_subsumption:       1222
% 3.84/0.97  res_orphan_elimination:                 0
% 3.84/0.97  res_tautology_del:                      286
% 3.84/0.97  res_num_eq_res_simplified:              0
% 3.84/0.97  res_num_sel_changes:                    0
% 3.84/0.97  res_moves_from_active_to_pass:          0
% 3.84/0.97  
% 3.84/0.97  ------ Superposition
% 3.84/0.97  
% 3.84/0.97  sup_time_total:                         0.
% 3.84/0.97  sup_time_generating:                    0.
% 3.84/0.97  sup_time_sim_full:                      0.
% 3.84/0.97  sup_time_sim_immed:                     0.
% 3.84/0.97  
% 3.84/0.97  sup_num_of_clauses:                     222
% 3.84/0.97  sup_num_in_active:                      130
% 3.84/0.97  sup_num_in_passive:                     92
% 3.84/0.97  sup_num_of_loops:                       138
% 3.84/0.97  sup_fw_superposition:                   299
% 3.84/0.97  sup_bw_superposition:                   144
% 3.84/0.97  sup_immediate_simplified:               132
% 3.84/0.97  sup_given_eliminated:                   1
% 3.84/0.97  comparisons_done:                       0
% 3.84/0.97  comparisons_avoided:                    0
% 3.84/0.97  
% 3.84/0.97  ------ Simplifications
% 3.84/0.97  
% 3.84/0.97  
% 3.84/0.97  sim_fw_subset_subsumed:                 38
% 3.84/0.97  sim_bw_subset_subsumed:                 13
% 3.84/0.97  sim_fw_subsumed:                        75
% 3.84/0.97  sim_bw_subsumed:                        5
% 3.84/0.97  sim_fw_subsumption_res:                 0
% 3.84/0.97  sim_bw_subsumption_res:                 0
% 3.84/0.97  sim_tautology_del:                      38
% 3.84/0.97  sim_eq_tautology_del:                   21
% 3.84/0.97  sim_eq_res_simp:                        0
% 3.84/0.97  sim_fw_demodulated:                     7
% 3.84/0.97  sim_bw_demodulated:                     1
% 3.84/0.97  sim_light_normalised:                   27
% 3.84/0.97  sim_joinable_taut:                      0
% 3.84/0.97  sim_joinable_simp:                      0
% 3.84/0.97  sim_ac_normalised:                      0
% 3.84/0.97  sim_smt_subsumption:                    0
% 3.84/0.97  
%------------------------------------------------------------------------------
