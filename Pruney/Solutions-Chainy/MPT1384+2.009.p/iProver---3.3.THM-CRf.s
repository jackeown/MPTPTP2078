%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:25 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  189 (2767 expanded)
%              Number of clauses        :  120 ( 574 expanded)
%              Number of leaves         :   17 ( 798 expanded)
%              Depth                    :   34
%              Number of atoms          :  897 (28978 expanded)
%              Number of equality atoms :  203 ( 857 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK1(X0,X1,X2),X2)
            & r2_hidden(sK1(X0,X1,X2),X1)
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f24])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f42,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK5(X4),X1)
        & m1_connsp_2(sK5(X4),X0,X4)
        & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f38,f42,f41,f40,f39])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ! [X4] :
      ( m1_connsp_2(sK5(X4),sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f35,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | ~ m1_connsp_2(X3,sK2,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

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

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X4] :
      ( r1_tarski(sK5(X4),sK3)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_177,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_178,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X1,X0,X2),X0)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_178])).

cnf(c_367,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_368,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_367])).

cnf(c_426,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_234,c_368])).

cnf(c_1209,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X2,X0),X1)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0,X2),X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_178])).

cnf(c_427,plain,
    ( m1_subset_1(sK1(X0,X1,X2),X0)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_235,c_368])).

cnf(c_1208,plain,
    ( m1_subset_1(sK1(X0,X1,X2),X0) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1214,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1216,plain,
    ( m1_connsp_2(sK5(X0),sK2,X0) = iProver_top
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1215,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1222,plain,
    ( m1_connsp_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,k1_tops_1(X1,X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3475,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1222])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1221,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3758,plain,
    ( m1_connsp_2(sK3,sK2,X0) = iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1221])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_41,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_42,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK2,sK4)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1220,plain,
    ( m1_connsp_2(X0,sK2,sK4) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1634,plain,
    ( m1_connsp_2(sK3,sK2,sK4) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1220])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2152,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2153,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2152])).

cnf(c_2025,plain,
    ( m1_connsp_2(X0,sK2,sK4)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,X0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2533,plain,
    ( m1_connsp_2(sK3,sK2,sK4)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_2534,plain,
    ( m1_connsp_2(sK3,sK2,sK4) = iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2533])).

cnf(c_4067,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3758,c_28,c_29,c_30,c_31,c_41,c_42,c_1634,c_2153,c_2534])).

cnf(c_4252,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_connsp_2(sK5(X0),sK2,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3475,c_28,c_29,c_30,c_31,c_41,c_42,c_1634,c_2153,c_2534])).

cnf(c_4253,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4252])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1236,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4264,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK5(X0)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4253,c_1236])).

cnf(c_5203,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),X2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_4264])).

cnf(c_3657,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k1_tops_1(X1,X0))
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_12,c_2])).

cnf(c_4069,plain,
    ( ~ v3_pre_topc(sK3,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4067])).

cnf(c_8441,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_4069])).

cnf(c_9659,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_16,c_8441])).

cnf(c_4254,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4253])).

cnf(c_10111,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_connsp_2(sK5(X0),sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9659,c_4254])).

cnf(c_10112,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_10111])).

cnf(c_11320,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK5(X0),X2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_3657,c_10112])).

cnf(c_5233,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK5(X0),X2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5203])).

cnf(c_12091,plain,
    ( ~ r1_tarski(sK5(X0),X2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11320,c_25,c_5233,c_8441])).

cnf(c_12092,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK5(X0),X2) ),
    inference(renaming,[status(thm)],[c_12091])).

cnf(c_12093,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12092])).

cnf(c_14403,plain,
    ( r1_tarski(sK5(X0),X2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X2)) = iProver_top
    | m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5203,c_12093])).

cnf(c_14404,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_14403])).

cnf(c_14414,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,X1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_14404])).

cnf(c_14589,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,X1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14414,c_28,c_29,c_30,c_31,c_41,c_42,c_1634,c_2153,c_2534])).

cnf(c_14602,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK5(X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_14589])).

cnf(c_12135,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK3))
    | ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK5(X0),sK3) ),
    inference(resolution,[status(thm)],[c_12092,c_24])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK5(X0),sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12348,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,k1_tops_1(sK2,sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_connsp_2(sK5(X0),sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12135,c_21,c_4069])).

cnf(c_12349,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK3))
    | ~ r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_12348])).

cnf(c_8418,negated_conjecture,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_4069])).

cnf(c_12378,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_tops_1(sK2,sK3))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_12349,c_8418])).

cnf(c_12379,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12378])).

cnf(c_14920,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14602,c_12379])).

cnf(c_14921,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_14920])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0,X2),X2)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_178])).

cnf(c_425,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_233,c_368])).

cnf(c_1210,plain,
    ( r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_14929,plain,
    ( m1_subset_1(sK1(X0,X1,k1_tops_1(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(X0,X1,k1_tops_1(sK2,sK3)),sK3) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,k1_tops_1(sK2,sK3)) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14921,c_1210])).

cnf(c_16786,plain,
    ( r2_hidden(sK1(u1_struct_0(sK2),X0,k1_tops_1(sK2,sK3)),sK3) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_14929])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2518,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_11,c_24])).

cnf(c_1584,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2815,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2518,c_25,c_24,c_1584])).

cnf(c_2827,plain,
    ( ~ r2_hidden(X0,k1_tops_1(sK2,sK3))
    | r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_2815,c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2923,plain,
    ( r2_hidden(sK0(k1_tops_1(sK2,sK3),X0),sK3)
    | r1_tarski(k1_tops_1(sK2,sK3),X0) ),
    inference(resolution,[status(thm)],[c_2827,c_1])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1656,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_24])).

cnf(c_1935,plain,
    ( r2_hidden(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_2,c_1656])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1987,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),sK3)
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_1935,c_0])).

cnf(c_3063,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_2923,c_1987])).

cnf(c_3064,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3063])).

cnf(c_19271,plain,
    ( r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK2),X0,k1_tops_1(sK2,sK3)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16786,c_3064])).

cnf(c_19272,plain,
    ( r2_hidden(sK1(u1_struct_0(sK2),X0,k1_tops_1(sK2,sK3)),sK3) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_19271])).

cnf(c_19280,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK2,sK3)) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_19272])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_509,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2136,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_3,c_509])).

cnf(c_2831,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | l1_pre_topc(k1_tops_1(sK2,sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_2815,c_2136])).

cnf(c_13,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_499,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_13])).

cnf(c_500,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_13])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_13])).

cnf(c_805,plain,
    ( k1_tops_1(X1,X0) != X0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_500,c_498])).

cnf(c_806,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_805])).

cnf(c_1620,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_1621,plain,
    ( k1_tops_1(sK2,sK3) != sK3
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1620])).

cnf(c_1662,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2928,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2831,c_28,c_29,c_25,c_30,c_24,c_31,c_41,c_42,c_1584,c_1621,c_1634,c_1662,c_2153,c_2534])).

cnf(c_2930,plain,
    ( r1_tarski(sK3,k1_tops_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2928])).

cnf(c_1657,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19280,c_3064,c_2930,c_1657])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.88/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.98  
% 3.88/0.98  ------  iProver source info
% 3.88/0.98  
% 3.88/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.98  git: non_committed_changes: false
% 3.88/0.98  git: last_make_outside_of_git: false
% 3.88/0.98  
% 3.88/0.98  ------ 
% 3.88/0.98  ------ Parsing...
% 3.88/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.98  ------ Proving...
% 3.88/0.98  ------ Problem Properties 
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  clauses                                 31
% 3.88/0.98  conjectures                             10
% 3.88/0.98  EPR                                     9
% 3.88/0.98  Horn                                    20
% 3.88/0.98  unary                                   5
% 3.88/0.98  binary                                  8
% 3.88/0.98  lits                                    103
% 3.88/0.98  lits eq                                 3
% 3.88/0.98  fd_pure                                 0
% 3.88/0.98  fd_pseudo                               0
% 3.88/0.98  fd_cond                                 0
% 3.88/0.98  fd_pseudo_cond                          1
% 3.88/0.98  AC symbols                              0
% 3.88/0.98  
% 3.88/0.98  ------ Input Options Time Limit: Unbounded
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  ------ 
% 3.88/0.98  Current options:
% 3.88/0.98  ------ 
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  ------ Proving...
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  % SZS status Theorem for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  fof(f3,axiom,(
% 3.88/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f13,plain,(
% 3.88/0.98    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f3])).
% 3.88/0.98  
% 3.88/0.98  fof(f14,plain,(
% 3.88/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.88/0.98    inference(flattening,[],[f13])).
% 3.88/0.98  
% 3.88/0.98  fof(f32,plain,(
% 3.88/0.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),X0)))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f33,plain,(
% 3.88/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f32])).
% 3.88/0.98  
% 3.88/0.98  fof(f51,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f33])).
% 3.88/0.98  
% 3.88/0.98  fof(f4,axiom,(
% 3.88/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f34,plain,(
% 3.88/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.88/0.98    inference(nnf_transformation,[],[f4])).
% 3.88/0.98  
% 3.88/0.98  fof(f54,plain,(
% 3.88/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f34])).
% 3.88/0.98  
% 3.88/0.98  fof(f50,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f33])).
% 3.88/0.98  
% 3.88/0.98  fof(f10,conjecture,(
% 3.88/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f11,negated_conjecture,(
% 3.88/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.88/0.98    inference(negated_conjecture,[],[f10])).
% 3.88/0.98  
% 3.88/0.98  fof(f24,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f11])).
% 3.88/0.98  
% 3.88/0.98  fof(f25,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.88/0.98    inference(flattening,[],[f24])).
% 3.88/0.98  
% 3.88/0.98  fof(f36,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.88/0.98    inference(nnf_transformation,[],[f25])).
% 3.88/0.98  
% 3.88/0.98  fof(f37,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.88/0.98    inference(flattening,[],[f36])).
% 3.88/0.98  
% 3.88/0.98  fof(f38,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.88/0.98    inference(rectify,[],[f37])).
% 3.88/0.98  
% 3.88/0.98  fof(f42,plain,(
% 3.88/0.98    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK5(X4),X1) & m1_connsp_2(sK5(X4),X0,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f41,plain,(
% 3.88/0.98    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f40,plain,(
% 3.88/0.98    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK3,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK3) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f39,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK2,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f43,plain,(
% 3.88/0.98    (((! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) & (! [X4] : ((r1_tarski(sK5(X4),sK3) & m1_connsp_2(sK5(X4),sK2,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f38,f42,f41,f40,f39])).
% 3.88/0.98  
% 3.88/0.98  fof(f65,plain,(
% 3.88/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f67,plain,(
% 3.88/0.98    ( ! [X4] : (m1_connsp_2(sK5(X4),sK2,X4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f6,axiom,(
% 3.88/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f16,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f6])).
% 3.88/0.98  
% 3.88/0.98  fof(f17,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.88/0.98    inference(flattening,[],[f16])).
% 3.88/0.98  
% 3.88/0.98  fof(f56,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f17])).
% 3.88/0.98  
% 3.88/0.98  fof(f66,plain,(
% 3.88/0.98    ( ! [X4] : (m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f8,axiom,(
% 3.88/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f20,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f8])).
% 3.88/0.98  
% 3.88/0.98  fof(f21,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.88/0.98    inference(flattening,[],[f20])).
% 3.88/0.98  
% 3.88/0.98  fof(f35,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.88/0.98    inference(nnf_transformation,[],[f21])).
% 3.88/0.98  
% 3.88/0.98  fof(f59,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f35])).
% 3.88/0.98  
% 3.88/0.98  fof(f62,plain,(
% 3.88/0.98    ~v2_struct_0(sK2)),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f63,plain,(
% 3.88/0.98    v2_pre_topc(sK2)),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f64,plain,(
% 3.88/0.98    l1_pre_topc(sK2)),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f9,axiom,(
% 3.88/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f22,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f9])).
% 3.88/0.98  
% 3.88/0.98  fof(f23,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.88/0.98    inference(flattening,[],[f22])).
% 3.88/0.98  
% 3.88/0.98  fof(f61,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f23])).
% 3.88/0.98  
% 3.88/0.98  fof(f69,plain,(
% 3.88/0.98    m1_subset_1(sK4,u1_struct_0(sK2)) | ~v3_pre_topc(sK3,sK2)),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f70,plain,(
% 3.88/0.98    r2_hidden(sK4,sK3) | ~v3_pre_topc(sK3,sK2)),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f71,plain,(
% 3.88/0.98    ( ! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f2,axiom,(
% 3.88/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f30,plain,(
% 3.88/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.88/0.98    inference(nnf_transformation,[],[f2])).
% 3.88/0.98  
% 3.88/0.98  fof(f31,plain,(
% 3.88/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.88/0.98    inference(flattening,[],[f30])).
% 3.88/0.98  
% 3.88/0.98  fof(f47,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.88/0.98    inference(cnf_transformation,[],[f31])).
% 3.88/0.98  
% 3.88/0.98  fof(f73,plain,(
% 3.88/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.88/0.98    inference(equality_resolution,[],[f47])).
% 3.88/0.98  
% 3.88/0.98  fof(f1,axiom,(
% 3.88/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f12,plain,(
% 3.88/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f1])).
% 3.88/0.98  
% 3.88/0.98  fof(f26,plain,(
% 3.88/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.98    inference(nnf_transformation,[],[f12])).
% 3.88/0.98  
% 3.88/0.98  fof(f27,plain,(
% 3.88/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.98    inference(rectify,[],[f26])).
% 3.88/0.98  
% 3.88/0.98  fof(f28,plain,(
% 3.88/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f29,plain,(
% 3.88/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.88/0.98  
% 3.88/0.98  fof(f44,plain,(
% 3.88/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f29])).
% 3.88/0.98  
% 3.88/0.98  fof(f68,plain,(
% 3.88/0.98    ( ! [X4] : (r1_tarski(sK5(X4),sK3) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f52,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f33])).
% 3.88/0.98  
% 3.88/0.98  fof(f5,axiom,(
% 3.88/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f15,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f5])).
% 3.88/0.98  
% 3.88/0.98  fof(f55,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f15])).
% 3.88/0.98  
% 3.88/0.98  fof(f45,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f29])).
% 3.88/0.98  
% 3.88/0.98  fof(f53,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f34])).
% 3.88/0.98  
% 3.88/0.98  fof(f46,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f29])).
% 3.88/0.98  
% 3.88/0.98  fof(f49,plain,(
% 3.88/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f31])).
% 3.88/0.98  
% 3.88/0.98  fof(f7,axiom,(
% 3.88/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f18,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f7])).
% 3.88/0.98  
% 3.88/0.98  fof(f19,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.88/0.98    inference(flattening,[],[f18])).
% 3.88/0.98  
% 3.88/0.98  fof(f58,plain,(
% 3.88/0.98    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f19])).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.88/0.98      | r2_hidden(sK1(X1,X2,X0),X2)
% 3.88/0.98      | r1_tarski(X2,X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_9,plain,
% 3.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_177,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.88/0.98      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_178,plain,
% 3.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_177]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_234,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.98      | r2_hidden(sK1(X1,X0,X2),X0)
% 3.88/0.98      | ~ r1_tarski(X2,X1)
% 3.88/0.98      | r1_tarski(X0,X2) ),
% 3.88/0.98      inference(bin_hyper_res,[status(thm)],[c_7,c_178]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_367,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.88/0.98      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_368,plain,
% 3.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_367]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_426,plain,
% 3.88/0.98      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.88/0.98      | ~ r1_tarski(X1,X0)
% 3.88/0.98      | ~ r1_tarski(X2,X0)
% 3.88/0.98      | r1_tarski(X1,X2) ),
% 3.88/0.98      inference(bin_hyper_res,[status(thm)],[c_234,c_368]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1209,plain,
% 3.88/0.98      ( r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
% 3.88/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.88/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.88/0.98      | r1_tarski(X1,X2) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.88/0.98      | m1_subset_1(sK1(X1,X2,X0),X1)
% 3.88/0.98      | r1_tarski(X2,X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_235,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.98      | m1_subset_1(sK1(X1,X0,X2),X1)
% 3.88/0.98      | ~ r1_tarski(X2,X1)
% 3.88/0.98      | r1_tarski(X0,X2) ),
% 3.88/0.98      inference(bin_hyper_res,[status(thm)],[c_8,c_178]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_427,plain,
% 3.88/0.98      ( m1_subset_1(sK1(X0,X1,X2),X0)
% 3.88/0.98      | ~ r1_tarski(X1,X0)
% 3.88/0.98      | ~ r1_tarski(X2,X0)
% 3.88/0.98      | r1_tarski(X1,X2) ),
% 3.88/0.98      inference(bin_hyper_res,[status(thm)],[c_235,c_368]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1208,plain,
% 3.88/0.98      ( m1_subset_1(sK1(X0,X1,X2),X0) = iProver_top
% 3.88/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.88/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.88/0.98      | r1_tarski(X1,X2) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_24,negated_conjecture,
% 3.88/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.88/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1214,plain,
% 3.88/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_22,negated_conjecture,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X0)
% 3.88/0.98      | v3_pre_topc(sK3,sK2)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1216,plain,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X0) = iProver_top
% 3.88/0.98      | v3_pre_topc(sK3,sK2) = iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ r1_tarski(X0,X2)
% 3.88/0.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.88/0.98      | ~ l1_pre_topc(X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1230,plain,
% 3.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.88/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.88/0.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
% 3.88/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_23,negated_conjecture,
% 3.88/0.98      ( v3_pre_topc(sK3,sK2)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1215,plain,
% 3.88/0.98      ( v3_pre_topc(sK3,sK2) = iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_16,plain,
% 3.88/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.88/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.88/0.98      | v2_struct_0(X1)
% 3.88/0.98      | ~ v2_pre_topc(X1)
% 3.88/0.98      | ~ l1_pre_topc(X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1222,plain,
% 3.88/0.98      ( m1_connsp_2(X0,X1,X2) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.88/0.98      | r2_hidden(X2,k1_tops_1(X1,X0)) = iProver_top
% 3.88/0.98      | v2_struct_0(X1) = iProver_top
% 3.88/0.98      | v2_pre_topc(X1) != iProver_top
% 3.88/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3475,plain,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 3.88/0.98      | v3_pre_topc(sK3,sK2) = iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | v2_struct_0(sK2) = iProver_top
% 3.88/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.88/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1215,c_1222]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_27,negated_conjecture,
% 3.88/0.98      ( ~ v2_struct_0(sK2) ),
% 3.88/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_28,plain,
% 3.88/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_26,negated_conjecture,
% 3.88/0.98      ( v2_pre_topc(sK2) ),
% 3.88/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_29,plain,
% 3.88/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_25,negated_conjecture,
% 3.88/0.98      ( l1_pre_topc(sK2) ),
% 3.88/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_30,plain,
% 3.88/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_17,plain,
% 3.88/0.98      ( m1_connsp_2(X0,X1,X2)
% 3.88/0.98      | ~ v3_pre_topc(X0,X1)
% 3.88/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ r2_hidden(X2,X0)
% 3.88/0.98      | v2_struct_0(X1)
% 3.88/0.98      | ~ v2_pre_topc(X1)
% 3.88/0.98      | ~ l1_pre_topc(X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1221,plain,
% 3.88/0.98      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 3.88/0.98      | v3_pre_topc(X0,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.88/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.88/0.98      | v2_struct_0(X1) = iProver_top
% 3.88/0.98      | v2_pre_topc(X1) != iProver_top
% 3.88/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3758,plain,
% 3.88/0.98      ( m1_connsp_2(sK3,sK2,X0) = iProver_top
% 3.88/0.98      | v3_pre_topc(sK3,sK2) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | v2_struct_0(sK2) = iProver_top
% 3.88/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.88/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1214,c_1221]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_31,plain,
% 3.88/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_20,negated_conjecture,
% 3.88/0.98      ( ~ v3_pre_topc(sK3,sK2) | m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_41,plain,
% 3.88/0.98      ( v3_pre_topc(sK3,sK2) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_19,negated_conjecture,
% 3.88/0.98      ( ~ v3_pre_topc(sK3,sK2) | r2_hidden(sK4,sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_42,plain,
% 3.88/0.98      ( v3_pre_topc(sK3,sK2) != iProver_top
% 3.88/0.98      | r2_hidden(sK4,sK3) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_18,negated_conjecture,
% 3.88/0.98      ( ~ m1_connsp_2(X0,sK2,sK4)
% 3.88/0.98      | ~ v3_pre_topc(sK3,sK2)
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | ~ r1_tarski(X0,sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1220,plain,
% 3.88/0.98      ( m1_connsp_2(X0,sK2,sK4) != iProver_top
% 3.88/0.98      | v3_pre_topc(sK3,sK2) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | r1_tarski(X0,sK3) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1634,plain,
% 3.88/0.98      ( m1_connsp_2(sK3,sK2,sK4) != iProver_top
% 3.88/0.98      | v3_pre_topc(sK3,sK2) != iProver_top
% 3.88/0.98      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1214,c_1220]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5,plain,
% 3.88/0.98      ( r1_tarski(X0,X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2152,plain,
% 3.88/0.98      ( r1_tarski(sK3,sK3) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2153,plain,
% 3.88/0.98      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_2152]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2025,plain,
% 3.88/0.98      ( m1_connsp_2(X0,sK2,sK4)
% 3.88/0.98      | ~ v3_pre_topc(X0,sK2)
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.88/0.98      | ~ r2_hidden(sK4,X0)
% 3.88/0.98      | v2_struct_0(sK2)
% 3.88/0.98      | ~ v2_pre_topc(sK2)
% 3.88/0.98      | ~ l1_pre_topc(sK2) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2533,plain,
% 3.88/0.98      ( m1_connsp_2(sK3,sK2,sK4)
% 3.88/0.98      | ~ v3_pre_topc(sK3,sK2)
% 3.88/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | ~ r2_hidden(sK4,sK3)
% 3.88/0.98      | v2_struct_0(sK2)
% 3.88/0.98      | ~ v2_pre_topc(sK2)
% 3.88/0.98      | ~ l1_pre_topc(sK2) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_2025]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2534,plain,
% 3.88/0.98      ( m1_connsp_2(sK3,sK2,sK4) = iProver_top
% 3.88/0.98      | v3_pre_topc(sK3,sK2) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | r2_hidden(sK4,sK3) != iProver_top
% 3.88/0.98      | v2_struct_0(sK2) = iProver_top
% 3.88/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.88/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_2533]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4067,plain,
% 3.88/0.98      ( v3_pre_topc(sK3,sK2) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_3758,c_28,c_29,c_30,c_31,c_41,c_42,c_1634,c_2153,
% 3.88/0.98                 c_2534]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4252,plain,
% 3.88/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
% 3.88/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_connsp_2(sK5(X0),sK2,X1) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_3475,c_28,c_29,c_30,c_31,c_41,c_42,c_1634,c_2153,
% 3.88/0.98                 c_2534]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4253,plain,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_4252]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2,plain,
% 3.88/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.88/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1236,plain,
% 3.88/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.88/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.88/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4264,plain,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(X1,X2) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r1_tarski(k1_tops_1(sK2,sK5(X0)),X2) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_4253,c_1236]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5203,plain,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,X2)) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r1_tarski(sK5(X0),X2) != iProver_top
% 3.88/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1230,c_4264]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3657,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ r2_hidden(X3,k1_tops_1(X1,X0))
% 3.88/0.98      | r2_hidden(X3,k1_tops_1(X1,X2))
% 3.88/0.98      | ~ r1_tarski(X0,X2)
% 3.88/0.98      | ~ l1_pre_topc(X1) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_12,c_2]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4069,plain,
% 3.88/0.98      ( ~ v3_pre_topc(sK3,sK2) ),
% 3.88/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4067]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8441,negated_conjecture,
% 3.88/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_23,c_4069]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_9659,plain,
% 3.88/0.98      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 3.88/0.98      | ~ r2_hidden(X0,sK3)
% 3.88/0.98      | v2_struct_0(sK2)
% 3.88/0.98      | ~ v2_pre_topc(sK2)
% 3.88/0.98      | ~ l1_pre_topc(sK2) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_16,c_8441]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4254,plain,
% 3.88/0.98      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 3.88/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4253]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_10111,plain,
% 3.88/0.98      ( ~ r2_hidden(X0,sK3)
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_connsp_2(sK5(X0),sK2,X1) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_9659,c_4254]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_10112,plain,
% 3.88/0.98      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 3.88/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_10111]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_11320,plain,
% 3.88/0.98      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 3.88/0.98      | ~ r2_hidden(X0,sK3)
% 3.88/0.98      | ~ r1_tarski(sK5(X0),X2)
% 3.88/0.98      | ~ l1_pre_topc(sK2) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_3657,c_10112]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5233,plain,
% 3.88/0.98      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 3.88/0.98      | ~ r2_hidden(X0,sK3)
% 3.88/0.98      | ~ r1_tarski(sK5(X0),X2)
% 3.88/0.98      | ~ l1_pre_topc(sK2) ),
% 3.88/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_5203]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12091,plain,
% 3.88/0.98      ( ~ r1_tarski(sK5(X0),X2)
% 3.88/0.98      | ~ r2_hidden(X0,sK3)
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 3.88/0.98      | ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_11320,c_25,c_5233,c_8441]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12092,plain,
% 3.88/0.98      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 3.88/0.98      | ~ r2_hidden(X0,sK3)
% 3.88/0.98      | ~ r1_tarski(sK5(X0),X2) ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_12091]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12093,plain,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,X2)) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r1_tarski(sK5(X0),X2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_12092]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14403,plain,
% 3.88/0.98      ( r1_tarski(sK5(X0),X2) != iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,X2)) = iProver_top
% 3.88/0.98      | m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_5203,c_12093]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14404,plain,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,X2)) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r1_tarski(sK5(X0),X2) != iProver_top ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_14403]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14414,plain,
% 3.88/0.98      ( v3_pre_topc(sK3,sK2) = iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | r2_hidden(X0,k1_tops_1(sK2,X1)) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r1_tarski(sK5(X0),X1) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1216,c_14404]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14589,plain,
% 3.88/0.98      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | r2_hidden(X0,k1_tops_1(sK2,X1)) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r1_tarski(sK5(X0),X1) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_14414,c_28,c_29,c_30,c_31,c_41,c_42,c_1634,c_2153,
% 3.88/0.98                 c_2534]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14602,plain,
% 3.88/0.98      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r1_tarski(sK5(X0),sK3) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1214,c_14589]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12135,plain,
% 3.88/0.98      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK3))
% 3.88/0.98      | ~ r2_hidden(X0,sK3)
% 3.88/0.98      | ~ r1_tarski(sK5(X0),sK3) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_12092,c_24]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_21,negated_conjecture,
% 3.88/0.98      ( v3_pre_topc(sK3,sK2)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ r2_hidden(X0,sK3)
% 3.88/0.98      | r1_tarski(sK5(X0),sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12348,plain,
% 3.88/0.98      ( ~ r2_hidden(X0,sK3)
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK3))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_connsp_2(sK5(X0),sK2,X1) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_12135,c_21,c_4069]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12349,plain,
% 3.88/0.98      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.88/0.98      | r2_hidden(X1,k1_tops_1(sK2,sK3))
% 3.88/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_12348]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8418,negated_conjecture,
% 3.88/0.98      ( m1_connsp_2(sK5(X0),sK2,X0)
% 3.88/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_22,c_4069]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12378,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.88/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK3))
% 3.88/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_12349,c_8418]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_12379,plain,
% 3.88/0.98      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_12378]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14920,plain,
% 3.88/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 3.88/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_14602,c_12379]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14921,plain,
% 3.88/0.98      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_14920]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.88/0.98      | ~ r2_hidden(sK1(X1,X2,X0),X0)
% 3.88/0.98      | r1_tarski(X2,X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_233,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.98      | ~ r2_hidden(sK1(X1,X0,X2),X2)
% 3.88/0.98      | ~ r1_tarski(X2,X1)
% 3.88/0.98      | r1_tarski(X0,X2) ),
% 3.88/0.98      inference(bin_hyper_res,[status(thm)],[c_6,c_178]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_425,plain,
% 3.88/0.98      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.88/0.98      | ~ r1_tarski(X1,X0)
% 3.88/0.98      | ~ r1_tarski(X2,X0)
% 3.88/0.98      | r1_tarski(X1,X2) ),
% 3.88/0.98      inference(bin_hyper_res,[status(thm)],[c_233,c_368]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1210,plain,
% 3.88/0.98      ( r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 3.88/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.88/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.88/0.98      | r1_tarski(X1,X2) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14929,plain,
% 3.88/0.98      ( m1_subset_1(sK1(X0,X1,k1_tops_1(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r2_hidden(sK1(X0,X1,k1_tops_1(sK2,sK3)),sK3) != iProver_top
% 3.88/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.88/0.98      | r1_tarski(X1,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | r1_tarski(k1_tops_1(sK2,sK3),X0) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_14921,c_1210]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_16786,plain,
% 3.88/0.98      ( r2_hidden(sK1(u1_struct_0(sK2),X0,k1_tops_1(sK2,sK3)),sK3) != iProver_top
% 3.88/0.98      | r1_tarski(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1208,c_14929]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_11,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.88/0.98      | ~ l1_pre_topc(X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2518,plain,
% 3.88/0.98      ( r1_tarski(k1_tops_1(sK2,sK3),sK3) | ~ l1_pre_topc(sK2) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_11,c_24]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1584,plain,
% 3.88/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 3.88/0.98      | ~ l1_pre_topc(sK2) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2815,plain,
% 3.88/0.98      ( r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_2518,c_25,c_24,c_1584]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2827,plain,
% 3.88/0.98      ( ~ r2_hidden(X0,k1_tops_1(sK2,sK3)) | r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_2815,c_2]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1,plain,
% 3.88/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2923,plain,
% 3.88/0.98      ( r2_hidden(sK0(k1_tops_1(sK2,sK3),X0),sK3)
% 3.88/0.98      | r1_tarski(k1_tops_1(sK2,sK3),X0) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_2827,c_1]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_10,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1656,plain,
% 3.88/0.98      ( r1_tarski(sK3,u1_struct_0(sK2)) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_10,c_24]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1935,plain,
% 3.88/0.98      ( r2_hidden(X0,u1_struct_0(sK2)) | ~ r2_hidden(X0,sK3) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_2,c_1656]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_0,plain,
% 3.88/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1987,plain,
% 3.88/0.98      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),sK3)
% 3.88/0.98      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_1935,c_0]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3063,plain,
% 3.88/0.98      ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_2923,c_1987]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3064,plain,
% 3.88/0.98      ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_3063]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_19271,plain,
% 3.88/0.98      ( r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r1_tarski(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | r2_hidden(sK1(u1_struct_0(sK2),X0,k1_tops_1(sK2,sK3)),sK3) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_16786,c_3064]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_19272,plain,
% 3.88/0.98      ( r2_hidden(sK1(u1_struct_0(sK2),X0,k1_tops_1(sK2,sK3)),sK3) != iProver_top
% 3.88/0.98      | r1_tarski(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_19271]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_19280,plain,
% 3.88/0.98      ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) != iProver_top
% 3.88/0.98      | r1_tarski(sK3,k1_tops_1(sK2,sK3)) = iProver_top
% 3.88/0.98      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_1209,c_19272]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_509,plain,
% 3.88/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 3.88/0.98      theory(equality) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2136,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1)
% 3.88/0.98      | ~ r1_tarski(X1,X0)
% 3.88/0.98      | ~ l1_pre_topc(X0)
% 3.88/0.98      | l1_pre_topc(X1) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_3,c_509]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2831,plain,
% 3.88/0.98      ( ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 3.88/0.98      | l1_pre_topc(k1_tops_1(sK2,sK3))
% 3.88/0.98      | ~ l1_pre_topc(sK3) ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_2815,c_2136]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_13,plain,
% 3.88/0.98      ( v3_pre_topc(X0,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.88/0.98      | ~ v2_pre_topc(X1)
% 3.88/0.98      | ~ l1_pre_topc(X1)
% 3.88/0.98      | ~ l1_pre_topc(X3)
% 3.88/0.98      | k1_tops_1(X1,X0) != X0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_499,plain,
% 3.88/0.98      ( v3_pre_topc(X0,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ v2_pre_topc(X1)
% 3.88/0.98      | ~ l1_pre_topc(X1)
% 3.88/0.98      | k1_tops_1(X1,X0) != X0
% 3.88/0.98      | ~ sP3_iProver_split ),
% 3.88/0.98      inference(splitting,
% 3.88/0.98                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.88/0.98                [c_13]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_500,plain,
% 3.88/0.98      ( sP3_iProver_split | sP2_iProver_split ),
% 3.88/0.98      inference(splitting,
% 3.88/0.98                [splitting(split),new_symbols(definition,[])],
% 3.88/0.98                [c_13]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_498,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ l1_pre_topc(X1)
% 3.88/0.98      | ~ sP2_iProver_split ),
% 3.88/0.98      inference(splitting,
% 3.88/0.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.88/0.98                [c_13]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_805,plain,
% 3.88/0.98      ( k1_tops_1(X1,X0) != X0
% 3.88/0.98      | ~ l1_pre_topc(X1)
% 3.88/0.98      | ~ v2_pre_topc(X1)
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | v3_pre_topc(X0,X1) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_499,c_500,c_498]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_806,plain,
% 3.88/0.98      ( v3_pre_topc(X0,X1)
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.88/0.98      | ~ v2_pre_topc(X1)
% 3.88/0.98      | ~ l1_pre_topc(X1)
% 3.88/0.98      | k1_tops_1(X1,X0) != X0 ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_805]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1620,plain,
% 3.88/0.98      ( v3_pre_topc(sK3,sK2)
% 3.88/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.88/0.98      | ~ v2_pre_topc(sK2)
% 3.88/0.98      | ~ l1_pre_topc(sK2)
% 3.88/0.98      | k1_tops_1(sK2,sK3) != sK3 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_806]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1621,plain,
% 3.88/0.98      ( k1_tops_1(sK2,sK3) != sK3
% 3.88/0.98      | v3_pre_topc(sK3,sK2) = iProver_top
% 3.88/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.88/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.88/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_1620]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1662,plain,
% 3.88/0.98      ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 3.88/0.98      | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 3.88/0.98      | k1_tops_1(sK2,sK3) = sK3 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2928,plain,
% 3.88/0.98      ( ~ r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_2831,c_28,c_29,c_25,c_30,c_24,c_31,c_41,c_42,c_1584,
% 3.88/0.98                 c_1621,c_1634,c_1662,c_2153,c_2534]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2930,plain,
% 3.88/0.98      ( r1_tarski(sK3,k1_tops_1(sK2,sK3)) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_2928]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1657,plain,
% 3.88/0.98      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_1656]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(contradiction,plain,
% 3.88/0.98      ( $false ),
% 3.88/0.98      inference(minisat,[status(thm)],[c_19280,c_3064,c_2930,c_1657]) ).
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  ------                               Statistics
% 3.88/0.98  
% 3.88/0.98  ------ Selected
% 3.88/0.98  
% 3.88/0.98  total_time:                             0.483
% 3.88/0.98  
%------------------------------------------------------------------------------
