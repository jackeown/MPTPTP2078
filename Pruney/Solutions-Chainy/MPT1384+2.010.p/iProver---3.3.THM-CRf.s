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
% DateTime   : Thu Dec  3 12:18:25 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  167 (1318 expanded)
%              Number of clauses        :  108 ( 299 expanded)
%              Number of leaves         :   13 ( 373 expanded)
%              Depth                    :   32
%              Number of atoms          :  773 (13853 expanded)
%              Number of equality atoms :  177 ( 453 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f35,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK4(X4),X1)
        & m1_connsp_2(sK4(X4),X0,X4)
        & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f35,f34,f33,f32])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X4] :
      ( m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v3_pre_topc(sK2,sK1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X4] :
      ( m1_connsp_2(sK4(X4),sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v3_pre_topc(sK2,sK1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X4] :
      ( r1_tarski(sK4(X4),sK2)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ m1_connsp_2(X3,sK1,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f58,plain,
    ( r2_hidden(sK3,sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1743,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1734,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1735,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_1730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(sK4(X0),sK1,X0)
    | v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_246,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_247,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_251,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_247,c_21,c_20])).

cnf(c_477,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X2))
    | ~ r2_hidden(X0,sK2)
    | X1 != X0
    | sK4(X0) != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_251])).

cnf(c_478,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v3_pre_topc(sK2,sK1)
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_18])).

cnf(c_483,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_1724,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1742,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2738,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK4(X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_1742])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1739,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2652,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1739])).

cnf(c_3869,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK4(X0)),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2738,c_2652])).

cnf(c_3880,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r1_tarski(sK4(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_3869])).

cnf(c_4502,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,X1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_3880])).

cnf(c_4640,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,X1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4502,c_2652])).

cnf(c_4641,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r1_tarski(sK4(X1),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4640])).

cnf(c_4652,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_4641])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2)
    | r1_tarski(sK4(X0),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1736,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2762,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2652,c_1736])).

cnf(c_4678,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4652,c_2762])).

cnf(c_4679,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4678])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1744,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4687,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),sK2) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_1744])).

cnf(c_4831,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1743,c_4687])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_1896,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_1897,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1896])).

cnf(c_9,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_304,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_305,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_309,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_20])).

cnf(c_310,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_309])).

cnf(c_414,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_310])).

cnf(c_415,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_1367,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_415])).

cnf(c_1368,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_415])).

cnf(c_1366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_415])).

cnf(c_1446,plain,
    ( k1_tops_1(sK1,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1367,c_1368,c_1366])).

cnf(c_1447,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_1446])).

cnf(c_1899,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_1900,plain,
    ( k1_tops_1(sK1,sK2) != sK2
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1927,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2100,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2))
    | k1_tops_1(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_2101,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2100])).

cnf(c_5022,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4831,c_26,c_1897,c_1900,c_2101])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_329,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_330,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_334,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_20])).

cnf(c_335,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_366,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_335,c_20])).

cnf(c_367,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_1369,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_367])).

cnf(c_1732,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_1370,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_367])).

cnf(c_1399,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_1400,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_1728,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1366])).

cnf(c_1951,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1728])).

cnf(c_2296,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | k1_tops_1(sK1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1732,c_1399,c_1400,c_1951])).

cnf(c_2297,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2296])).

cnf(c_2304,plain,
    ( k1_tops_1(sK1,sK2) = sK2
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_2297])).

cnf(c_5027,plain,
    ( k1_tops_1(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_5022,c_2304])).

cnf(c_13,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK1,sK3)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_270,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_271,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_275,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_21,c_20])).

cnf(c_453,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X2))
    | ~ r1_tarski(X1,sK2)
    | X2 != X1
    | sK3 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_275])).

cnf(c_454,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_15])).

cnf(c_459,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK2) ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_1725,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK1,X0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_2406,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1725])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1968,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1971,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1968])).

cnf(c_2534,plain,
    ( r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2406,c_1971])).

cnf(c_2535,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2534])).

cnf(c_5289,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5027,c_2535])).

cnf(c_14,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_37,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5289,c_5022,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n009.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 20:59:11 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 2.17/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/0.97  
% 2.17/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.97  
% 2.17/0.97  ------  iProver source info
% 2.17/0.97  
% 2.17/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.97  git: non_committed_changes: false
% 2.17/0.97  git: last_make_outside_of_git: false
% 2.17/0.97  
% 2.17/0.97  ------ 
% 2.17/0.97  
% 2.17/0.97  ------ Input Options
% 2.17/0.97  
% 2.17/0.97  --out_options                           all
% 2.17/0.97  --tptp_safe_out                         true
% 2.17/0.97  --problem_path                          ""
% 2.17/0.97  --include_path                          ""
% 2.17/0.97  --clausifier                            res/vclausify_rel
% 2.17/0.97  --clausifier_options                    --mode clausify
% 2.17/0.97  --stdin                                 false
% 2.17/0.97  --stats_out                             all
% 2.17/0.97  
% 2.17/0.97  ------ General Options
% 2.17/0.97  
% 2.17/0.97  --fof                                   false
% 2.17/0.97  --time_out_real                         305.
% 2.17/0.97  --time_out_virtual                      -1.
% 2.17/0.97  --symbol_type_check                     false
% 2.17/0.97  --clausify_out                          false
% 2.17/0.97  --sig_cnt_out                           false
% 2.17/0.97  --trig_cnt_out                          false
% 2.17/0.97  --trig_cnt_out_tolerance                1.
% 2.17/0.97  --trig_cnt_out_sk_spl                   false
% 2.17/0.97  --abstr_cl_out                          false
% 2.17/0.97  
% 2.17/0.97  ------ Global Options
% 2.17/0.97  
% 2.17/0.97  --schedule                              default
% 2.17/0.97  --add_important_lit                     false
% 2.17/0.97  --prop_solver_per_cl                    1000
% 2.17/0.97  --min_unsat_core                        false
% 2.17/0.97  --soft_assumptions                      false
% 2.17/0.97  --soft_lemma_size                       3
% 2.17/0.97  --prop_impl_unit_size                   0
% 2.17/0.97  --prop_impl_unit                        []
% 2.17/0.97  --share_sel_clauses                     true
% 2.17/0.97  --reset_solvers                         false
% 2.17/0.97  --bc_imp_inh                            [conj_cone]
% 2.17/0.97  --conj_cone_tolerance                   3.
% 2.17/0.97  --extra_neg_conj                        none
% 2.17/0.97  --large_theory_mode                     true
% 2.17/0.97  --prolific_symb_bound                   200
% 2.17/0.97  --lt_threshold                          2000
% 2.17/0.97  --clause_weak_htbl                      true
% 2.17/0.97  --gc_record_bc_elim                     false
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing Options
% 2.17/0.97  
% 2.17/0.97  --preprocessing_flag                    true
% 2.17/0.97  --time_out_prep_mult                    0.1
% 2.17/0.97  --splitting_mode                        input
% 2.17/0.97  --splitting_grd                         true
% 2.17/0.97  --splitting_cvd                         false
% 2.17/0.97  --splitting_cvd_svl                     false
% 2.17/0.97  --splitting_nvd                         32
% 2.17/0.97  --sub_typing                            true
% 2.17/0.97  --prep_gs_sim                           true
% 2.17/0.97  --prep_unflatten                        true
% 2.17/0.97  --prep_res_sim                          true
% 2.17/0.97  --prep_upred                            true
% 2.17/0.97  --prep_sem_filter                       exhaustive
% 2.17/0.97  --prep_sem_filter_out                   false
% 2.17/0.97  --pred_elim                             true
% 2.17/0.97  --res_sim_input                         true
% 2.17/0.97  --eq_ax_congr_red                       true
% 2.17/0.97  --pure_diseq_elim                       true
% 2.17/0.97  --brand_transform                       false
% 2.17/0.97  --non_eq_to_eq                          false
% 2.17/0.97  --prep_def_merge                        true
% 2.17/0.97  --prep_def_merge_prop_impl              false
% 2.17/0.97  --prep_def_merge_mbd                    true
% 2.17/0.97  --prep_def_merge_tr_red                 false
% 2.17/0.97  --prep_def_merge_tr_cl                  false
% 2.17/0.97  --smt_preprocessing                     true
% 2.17/0.97  --smt_ac_axioms                         fast
% 2.17/0.97  --preprocessed_out                      false
% 2.17/0.97  --preprocessed_stats                    false
% 2.17/0.97  
% 2.17/0.97  ------ Abstraction refinement Options
% 2.17/0.97  
% 2.17/0.97  --abstr_ref                             []
% 2.17/0.97  --abstr_ref_prep                        false
% 2.17/0.97  --abstr_ref_until_sat                   false
% 2.17/0.97  --abstr_ref_sig_restrict                funpre
% 2.17/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.97  --abstr_ref_under                       []
% 2.17/0.97  
% 2.17/0.97  ------ SAT Options
% 2.17/0.97  
% 2.17/0.97  --sat_mode                              false
% 2.17/0.97  --sat_fm_restart_options                ""
% 2.17/0.97  --sat_gr_def                            false
% 2.17/0.97  --sat_epr_types                         true
% 2.17/0.97  --sat_non_cyclic_types                  false
% 2.17/0.97  --sat_finite_models                     false
% 2.17/0.97  --sat_fm_lemmas                         false
% 2.17/0.97  --sat_fm_prep                           false
% 2.17/0.97  --sat_fm_uc_incr                        true
% 2.17/0.97  --sat_out_model                         small
% 2.17/0.97  --sat_out_clauses                       false
% 2.17/0.97  
% 2.17/0.97  ------ QBF Options
% 2.17/0.97  
% 2.17/0.97  --qbf_mode                              false
% 2.17/0.97  --qbf_elim_univ                         false
% 2.17/0.97  --qbf_dom_inst                          none
% 2.17/0.97  --qbf_dom_pre_inst                      false
% 2.17/0.97  --qbf_sk_in                             false
% 2.17/0.97  --qbf_pred_elim                         true
% 2.17/0.97  --qbf_split                             512
% 2.17/0.97  
% 2.17/0.97  ------ BMC1 Options
% 2.17/0.97  
% 2.17/0.97  --bmc1_incremental                      false
% 2.17/0.97  --bmc1_axioms                           reachable_all
% 2.17/0.97  --bmc1_min_bound                        0
% 2.17/0.97  --bmc1_max_bound                        -1
% 2.17/0.97  --bmc1_max_bound_default                -1
% 2.17/0.97  --bmc1_symbol_reachability              true
% 2.17/0.97  --bmc1_property_lemmas                  false
% 2.17/0.97  --bmc1_k_induction                      false
% 2.17/0.97  --bmc1_non_equiv_states                 false
% 2.17/0.97  --bmc1_deadlock                         false
% 2.17/0.97  --bmc1_ucm                              false
% 2.17/0.97  --bmc1_add_unsat_core                   none
% 2.17/0.97  --bmc1_unsat_core_children              false
% 2.17/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.97  --bmc1_out_stat                         full
% 2.17/0.97  --bmc1_ground_init                      false
% 2.17/0.97  --bmc1_pre_inst_next_state              false
% 2.17/0.97  --bmc1_pre_inst_state                   false
% 2.17/0.97  --bmc1_pre_inst_reach_state             false
% 2.17/0.97  --bmc1_out_unsat_core                   false
% 2.17/0.97  --bmc1_aig_witness_out                  false
% 2.17/0.97  --bmc1_verbose                          false
% 2.17/0.97  --bmc1_dump_clauses_tptp                false
% 2.17/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.97  --bmc1_dump_file                        -
% 2.17/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.97  --bmc1_ucm_extend_mode                  1
% 2.17/0.97  --bmc1_ucm_init_mode                    2
% 2.17/0.97  --bmc1_ucm_cone_mode                    none
% 2.17/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.97  --bmc1_ucm_relax_model                  4
% 2.17/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.97  --bmc1_ucm_layered_model                none
% 2.17/0.97  --bmc1_ucm_max_lemma_size               10
% 2.17/0.97  
% 2.17/0.97  ------ AIG Options
% 2.17/0.97  
% 2.17/0.97  --aig_mode                              false
% 2.17/0.97  
% 2.17/0.97  ------ Instantiation Options
% 2.17/0.97  
% 2.17/0.97  --instantiation_flag                    true
% 2.17/0.97  --inst_sos_flag                         false
% 2.17/0.97  --inst_sos_phase                        true
% 2.17/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.97  --inst_lit_sel_side                     num_symb
% 2.17/0.97  --inst_solver_per_active                1400
% 2.17/0.97  --inst_solver_calls_frac                1.
% 2.17/0.97  --inst_passive_queue_type               priority_queues
% 2.17/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.97  --inst_passive_queues_freq              [25;2]
% 2.17/0.97  --inst_dismatching                      true
% 2.17/0.97  --inst_eager_unprocessed_to_passive     true
% 2.17/0.97  --inst_prop_sim_given                   true
% 2.17/0.97  --inst_prop_sim_new                     false
% 2.17/0.97  --inst_subs_new                         false
% 2.17/0.97  --inst_eq_res_simp                      false
% 2.17/0.97  --inst_subs_given                       false
% 2.17/0.97  --inst_orphan_elimination               true
% 2.17/0.97  --inst_learning_loop_flag               true
% 2.17/0.97  --inst_learning_start                   3000
% 2.17/0.97  --inst_learning_factor                  2
% 2.17/0.97  --inst_start_prop_sim_after_learn       3
% 2.17/0.97  --inst_sel_renew                        solver
% 2.17/0.97  --inst_lit_activity_flag                true
% 2.17/0.97  --inst_restr_to_given                   false
% 2.17/0.97  --inst_activity_threshold               500
% 2.17/0.97  --inst_out_proof                        true
% 2.17/0.97  
% 2.17/0.97  ------ Resolution Options
% 2.17/0.97  
% 2.17/0.97  --resolution_flag                       true
% 2.17/0.97  --res_lit_sel                           adaptive
% 2.17/0.97  --res_lit_sel_side                      none
% 2.17/0.97  --res_ordering                          kbo
% 2.17/0.97  --res_to_prop_solver                    active
% 2.17/0.97  --res_prop_simpl_new                    false
% 2.17/0.97  --res_prop_simpl_given                  true
% 2.17/0.97  --res_passive_queue_type                priority_queues
% 2.17/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.97  --res_passive_queues_freq               [15;5]
% 2.17/0.97  --res_forward_subs                      full
% 2.17/0.97  --res_backward_subs                     full
% 2.17/0.97  --res_forward_subs_resolution           true
% 2.17/0.97  --res_backward_subs_resolution          true
% 2.17/0.97  --res_orphan_elimination                true
% 2.17/0.97  --res_time_limit                        2.
% 2.17/0.97  --res_out_proof                         true
% 2.17/0.97  
% 2.17/0.97  ------ Superposition Options
% 2.17/0.97  
% 2.17/0.97  --superposition_flag                    true
% 2.17/0.97  --sup_passive_queue_type                priority_queues
% 2.17/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.97  --demod_completeness_check              fast
% 2.17/0.97  --demod_use_ground                      true
% 2.17/0.97  --sup_to_prop_solver                    passive
% 2.17/0.97  --sup_prop_simpl_new                    true
% 2.17/0.97  --sup_prop_simpl_given                  true
% 2.17/0.97  --sup_fun_splitting                     false
% 2.17/0.97  --sup_smt_interval                      50000
% 2.17/0.97  
% 2.17/0.97  ------ Superposition Simplification Setup
% 2.17/0.97  
% 2.17/0.97  --sup_indices_passive                   []
% 2.17/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_full_bw                           [BwDemod]
% 2.17/0.97  --sup_immed_triv                        [TrivRules]
% 2.17/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_immed_bw_main                     []
% 2.17/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.97  
% 2.17/0.97  ------ Combination Options
% 2.17/0.97  
% 2.17/0.97  --comb_res_mult                         3
% 2.17/0.97  --comb_sup_mult                         2
% 2.17/0.97  --comb_inst_mult                        10
% 2.17/0.97  
% 2.17/0.97  ------ Debug Options
% 2.17/0.97  
% 2.17/0.97  --dbg_backtrace                         false
% 2.17/0.97  --dbg_dump_prop_clauses                 false
% 2.17/0.97  --dbg_dump_prop_clauses_file            -
% 2.17/0.97  --dbg_out_stat                          false
% 2.17/0.97  ------ Parsing...
% 2.17/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.97  ------ Proving...
% 2.17/0.97  ------ Problem Properties 
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  clauses                                 21
% 2.17/0.97  conjectures                             5
% 2.17/0.97  EPR                                     6
% 2.17/0.97  Horn                                    15
% 2.17/0.97  unary                                   2
% 2.17/0.97  binary                                  9
% 2.17/0.97  lits                                    57
% 2.17/0.97  lits eq                                 3
% 2.17/0.97  fd_pure                                 0
% 2.17/0.97  fd_pseudo                               0
% 2.17/0.97  fd_cond                                 0
% 2.17/0.97  fd_pseudo_cond                          1
% 2.17/0.97  AC symbols                              0
% 2.17/0.97  
% 2.17/0.97  ------ Schedule dynamic 5 is on 
% 2.17/0.97  
% 2.17/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  ------ 
% 2.17/0.97  Current options:
% 2.17/0.97  ------ 
% 2.17/0.97  
% 2.17/0.97  ------ Input Options
% 2.17/0.97  
% 2.17/0.97  --out_options                           all
% 2.17/0.97  --tptp_safe_out                         true
% 2.17/0.97  --problem_path                          ""
% 2.17/0.97  --include_path                          ""
% 2.17/0.97  --clausifier                            res/vclausify_rel
% 2.17/0.97  --clausifier_options                    --mode clausify
% 2.17/0.97  --stdin                                 false
% 2.17/0.97  --stats_out                             all
% 2.17/0.97  
% 2.17/0.97  ------ General Options
% 2.17/0.97  
% 2.17/0.97  --fof                                   false
% 2.17/0.97  --time_out_real                         305.
% 2.17/0.97  --time_out_virtual                      -1.
% 2.17/0.97  --symbol_type_check                     false
% 2.17/0.97  --clausify_out                          false
% 2.17/0.97  --sig_cnt_out                           false
% 2.17/0.97  --trig_cnt_out                          false
% 2.17/0.97  --trig_cnt_out_tolerance                1.
% 2.17/0.97  --trig_cnt_out_sk_spl                   false
% 2.17/0.97  --abstr_cl_out                          false
% 2.17/0.97  
% 2.17/0.97  ------ Global Options
% 2.17/0.97  
% 2.17/0.97  --schedule                              default
% 2.17/0.97  --add_important_lit                     false
% 2.17/0.97  --prop_solver_per_cl                    1000
% 2.17/0.97  --min_unsat_core                        false
% 2.17/0.97  --soft_assumptions                      false
% 2.17/0.97  --soft_lemma_size                       3
% 2.17/0.97  --prop_impl_unit_size                   0
% 2.17/0.97  --prop_impl_unit                        []
% 2.17/0.97  --share_sel_clauses                     true
% 2.17/0.97  --reset_solvers                         false
% 2.17/0.97  --bc_imp_inh                            [conj_cone]
% 2.17/0.97  --conj_cone_tolerance                   3.
% 2.17/0.97  --extra_neg_conj                        none
% 2.17/0.97  --large_theory_mode                     true
% 2.17/0.97  --prolific_symb_bound                   200
% 2.17/0.97  --lt_threshold                          2000
% 2.17/0.97  --clause_weak_htbl                      true
% 2.17/0.97  --gc_record_bc_elim                     false
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing Options
% 2.17/0.97  
% 2.17/0.97  --preprocessing_flag                    true
% 2.17/0.97  --time_out_prep_mult                    0.1
% 2.17/0.97  --splitting_mode                        input
% 2.17/0.97  --splitting_grd                         true
% 2.17/0.97  --splitting_cvd                         false
% 2.17/0.97  --splitting_cvd_svl                     false
% 2.17/0.97  --splitting_nvd                         32
% 2.17/0.97  --sub_typing                            true
% 2.17/0.97  --prep_gs_sim                           true
% 2.17/0.97  --prep_unflatten                        true
% 2.17/0.97  --prep_res_sim                          true
% 2.17/0.97  --prep_upred                            true
% 2.17/0.97  --prep_sem_filter                       exhaustive
% 2.17/0.97  --prep_sem_filter_out                   false
% 2.17/0.97  --pred_elim                             true
% 2.17/0.97  --res_sim_input                         true
% 2.17/0.97  --eq_ax_congr_red                       true
% 2.17/0.97  --pure_diseq_elim                       true
% 2.17/0.97  --brand_transform                       false
% 2.17/0.97  --non_eq_to_eq                          false
% 2.17/0.97  --prep_def_merge                        true
% 2.17/0.97  --prep_def_merge_prop_impl              false
% 2.17/0.97  --prep_def_merge_mbd                    true
% 2.17/0.97  --prep_def_merge_tr_red                 false
% 2.17/0.97  --prep_def_merge_tr_cl                  false
% 2.17/0.97  --smt_preprocessing                     true
% 2.17/0.97  --smt_ac_axioms                         fast
% 2.17/0.97  --preprocessed_out                      false
% 2.17/0.97  --preprocessed_stats                    false
% 2.17/0.97  
% 2.17/0.97  ------ Abstraction refinement Options
% 2.17/0.97  
% 2.17/0.97  --abstr_ref                             []
% 2.17/0.97  --abstr_ref_prep                        false
% 2.17/0.97  --abstr_ref_until_sat                   false
% 2.17/0.97  --abstr_ref_sig_restrict                funpre
% 2.17/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.97  --abstr_ref_under                       []
% 2.17/0.97  
% 2.17/0.97  ------ SAT Options
% 2.17/0.97  
% 2.17/0.97  --sat_mode                              false
% 2.17/0.97  --sat_fm_restart_options                ""
% 2.17/0.97  --sat_gr_def                            false
% 2.17/0.97  --sat_epr_types                         true
% 2.17/0.97  --sat_non_cyclic_types                  false
% 2.17/0.97  --sat_finite_models                     false
% 2.17/0.97  --sat_fm_lemmas                         false
% 2.17/0.97  --sat_fm_prep                           false
% 2.17/0.97  --sat_fm_uc_incr                        true
% 2.17/0.97  --sat_out_model                         small
% 2.17/0.97  --sat_out_clauses                       false
% 2.17/0.97  
% 2.17/0.97  ------ QBF Options
% 2.17/0.97  
% 2.17/0.97  --qbf_mode                              false
% 2.17/0.97  --qbf_elim_univ                         false
% 2.17/0.97  --qbf_dom_inst                          none
% 2.17/0.97  --qbf_dom_pre_inst                      false
% 2.17/0.97  --qbf_sk_in                             false
% 2.17/0.97  --qbf_pred_elim                         true
% 2.17/0.97  --qbf_split                             512
% 2.17/0.97  
% 2.17/0.97  ------ BMC1 Options
% 2.17/0.97  
% 2.17/0.97  --bmc1_incremental                      false
% 2.17/0.97  --bmc1_axioms                           reachable_all
% 2.17/0.97  --bmc1_min_bound                        0
% 2.17/0.97  --bmc1_max_bound                        -1
% 2.17/0.97  --bmc1_max_bound_default                -1
% 2.17/0.97  --bmc1_symbol_reachability              true
% 2.17/0.97  --bmc1_property_lemmas                  false
% 2.17/0.97  --bmc1_k_induction                      false
% 2.17/0.97  --bmc1_non_equiv_states                 false
% 2.17/0.97  --bmc1_deadlock                         false
% 2.17/0.97  --bmc1_ucm                              false
% 2.17/0.97  --bmc1_add_unsat_core                   none
% 2.17/0.97  --bmc1_unsat_core_children              false
% 2.17/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.97  --bmc1_out_stat                         full
% 2.17/0.97  --bmc1_ground_init                      false
% 2.17/0.97  --bmc1_pre_inst_next_state              false
% 2.17/0.97  --bmc1_pre_inst_state                   false
% 2.17/0.97  --bmc1_pre_inst_reach_state             false
% 2.17/0.97  --bmc1_out_unsat_core                   false
% 2.17/0.97  --bmc1_aig_witness_out                  false
% 2.17/0.97  --bmc1_verbose                          false
% 2.17/0.97  --bmc1_dump_clauses_tptp                false
% 2.17/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.97  --bmc1_dump_file                        -
% 2.17/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.97  --bmc1_ucm_extend_mode                  1
% 2.17/0.97  --bmc1_ucm_init_mode                    2
% 2.17/0.97  --bmc1_ucm_cone_mode                    none
% 2.17/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.97  --bmc1_ucm_relax_model                  4
% 2.17/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.97  --bmc1_ucm_layered_model                none
% 2.17/0.97  --bmc1_ucm_max_lemma_size               10
% 2.17/0.97  
% 2.17/0.97  ------ AIG Options
% 2.17/0.97  
% 2.17/0.97  --aig_mode                              false
% 2.17/0.97  
% 2.17/0.97  ------ Instantiation Options
% 2.17/0.97  
% 2.17/0.97  --instantiation_flag                    true
% 2.17/0.97  --inst_sos_flag                         false
% 2.17/0.97  --inst_sos_phase                        true
% 2.17/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.97  --inst_lit_sel_side                     none
% 2.17/0.97  --inst_solver_per_active                1400
% 2.17/0.97  --inst_solver_calls_frac                1.
% 2.17/0.97  --inst_passive_queue_type               priority_queues
% 2.17/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.97  --inst_passive_queues_freq              [25;2]
% 2.17/0.97  --inst_dismatching                      true
% 2.17/0.97  --inst_eager_unprocessed_to_passive     true
% 2.17/0.97  --inst_prop_sim_given                   true
% 2.17/0.97  --inst_prop_sim_new                     false
% 2.17/0.97  --inst_subs_new                         false
% 2.17/0.97  --inst_eq_res_simp                      false
% 2.17/0.97  --inst_subs_given                       false
% 2.17/0.97  --inst_orphan_elimination               true
% 2.17/0.97  --inst_learning_loop_flag               true
% 2.17/0.97  --inst_learning_start                   3000
% 2.17/0.97  --inst_learning_factor                  2
% 2.17/0.97  --inst_start_prop_sim_after_learn       3
% 2.17/0.97  --inst_sel_renew                        solver
% 2.17/0.97  --inst_lit_activity_flag                true
% 2.17/0.97  --inst_restr_to_given                   false
% 2.17/0.97  --inst_activity_threshold               500
% 2.17/0.97  --inst_out_proof                        true
% 2.17/0.97  
% 2.17/0.97  ------ Resolution Options
% 2.17/0.97  
% 2.17/0.97  --resolution_flag                       false
% 2.17/0.97  --res_lit_sel                           adaptive
% 2.17/0.97  --res_lit_sel_side                      none
% 2.17/0.97  --res_ordering                          kbo
% 2.17/0.97  --res_to_prop_solver                    active
% 2.17/0.97  --res_prop_simpl_new                    false
% 2.17/0.97  --res_prop_simpl_given                  true
% 2.17/0.97  --res_passive_queue_type                priority_queues
% 2.17/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.97  --res_passive_queues_freq               [15;5]
% 2.17/0.97  --res_forward_subs                      full
% 2.17/0.97  --res_backward_subs                     full
% 2.17/0.97  --res_forward_subs_resolution           true
% 2.17/0.97  --res_backward_subs_resolution          true
% 2.17/0.97  --res_orphan_elimination                true
% 2.17/0.97  --res_time_limit                        2.
% 2.17/0.97  --res_out_proof                         true
% 2.17/0.97  
% 2.17/0.97  ------ Superposition Options
% 2.17/0.97  
% 2.17/0.97  --superposition_flag                    true
% 2.17/0.97  --sup_passive_queue_type                priority_queues
% 2.17/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.97  --demod_completeness_check              fast
% 2.17/0.97  --demod_use_ground                      true
% 2.17/0.97  --sup_to_prop_solver                    passive
% 2.17/0.97  --sup_prop_simpl_new                    true
% 2.17/0.97  --sup_prop_simpl_given                  true
% 2.17/0.97  --sup_fun_splitting                     false
% 2.17/0.97  --sup_smt_interval                      50000
% 2.17/0.97  
% 2.17/0.97  ------ Superposition Simplification Setup
% 2.17/0.97  
% 2.17/0.97  --sup_indices_passive                   []
% 2.17/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_full_bw                           [BwDemod]
% 2.17/0.97  --sup_immed_triv                        [TrivRules]
% 2.17/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_immed_bw_main                     []
% 2.17/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.97  
% 2.17/0.97  ------ Combination Options
% 2.17/0.97  
% 2.17/0.97  --comb_res_mult                         3
% 2.17/0.97  --comb_sup_mult                         2
% 2.17/0.97  --comb_inst_mult                        10
% 2.17/0.97  
% 2.17/0.97  ------ Debug Options
% 2.17/0.97  
% 2.17/0.97  --dbg_backtrace                         false
% 2.17/0.97  --dbg_dump_prop_clauses                 false
% 2.17/0.97  --dbg_dump_prop_clauses_file            -
% 2.17/0.97  --dbg_out_stat                          false
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  ------ Proving...
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  % SZS status Theorem for theBenchmark.p
% 2.17/0.97  
% 2.17/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/0.97  
% 2.17/0.97  fof(f1,axiom,(
% 2.17/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.17/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f10,plain,(
% 2.17/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.17/0.97    inference(ennf_transformation,[],[f1])).
% 2.17/0.97  
% 2.17/0.97  fof(f22,plain,(
% 2.17/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.17/0.97    inference(nnf_transformation,[],[f10])).
% 2.17/0.97  
% 2.17/0.97  fof(f23,plain,(
% 2.17/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.17/0.97    inference(rectify,[],[f22])).
% 2.17/0.97  
% 2.17/0.97  fof(f24,plain,(
% 2.17/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.17/0.97    introduced(choice_axiom,[])).
% 2.17/0.97  
% 2.17/0.97  fof(f25,plain,(
% 2.17/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.17/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.17/0.97  
% 2.17/0.97  fof(f38,plain,(
% 2.17/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f25])).
% 2.17/0.97  
% 2.17/0.97  fof(f8,conjecture,(
% 2.17/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.17/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f9,negated_conjecture,(
% 2.17/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.17/0.97    inference(negated_conjecture,[],[f8])).
% 2.17/0.97  
% 2.17/0.97  fof(f20,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.17/0.97    inference(ennf_transformation,[],[f9])).
% 2.17/0.97  
% 2.17/0.97  fof(f21,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.17/0.97    inference(flattening,[],[f20])).
% 2.17/0.97  
% 2.17/0.97  fof(f29,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.17/0.97    inference(nnf_transformation,[],[f21])).
% 2.17/0.97  
% 2.17/0.97  fof(f30,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.17/0.97    inference(flattening,[],[f29])).
% 2.17/0.97  
% 2.17/0.97  fof(f31,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.17/0.97    inference(rectify,[],[f30])).
% 2.17/0.97  
% 2.17/0.97  fof(f35,plain,(
% 2.17/0.97    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK4(X4),X1) & m1_connsp_2(sK4(X4),X0,X4) & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.17/0.97    introduced(choice_axiom,[])).
% 2.17/0.97  
% 2.17/0.97  fof(f34,plain,(
% 2.17/0.97    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK3,X1) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.17/0.97    introduced(choice_axiom,[])).
% 2.17/0.97  
% 2.17/0.97  fof(f33,plain,(
% 2.17/0.97    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK2,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK2) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.17/0.97    introduced(choice_axiom,[])).
% 2.17/0.97  
% 2.17/0.97  fof(f32,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK1,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.17/0.97    introduced(choice_axiom,[])).
% 2.17/0.97  
% 2.17/0.97  fof(f36,plain,(
% 2.17/0.97    (((! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,sK1,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & r2_hidden(sK3,sK2) & m1_subset_1(sK3,u1_struct_0(sK1))) | ~v3_pre_topc(sK2,sK1)) & (! [X4] : ((r1_tarski(sK4(X4),sK2) & m1_connsp_2(sK4(X4),sK1,X4) & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.17/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f35,f34,f33,f32])).
% 2.17/0.97  
% 2.17/0.97  fof(f53,plain,(
% 2.17/0.97    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f54,plain,(
% 2.17/0.97    ( ! [X4] : (m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v3_pre_topc(sK2,sK1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f5,axiom,(
% 2.17/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.17/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f14,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.97    inference(ennf_transformation,[],[f5])).
% 2.17/0.97  
% 2.17/0.97  fof(f15,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.97    inference(flattening,[],[f14])).
% 2.17/0.97  
% 2.17/0.97  fof(f45,plain,(
% 2.17/0.97    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f15])).
% 2.17/0.97  
% 2.17/0.97  fof(f52,plain,(
% 2.17/0.97    l1_pre_topc(sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f55,plain,(
% 2.17/0.97    ( ! [X4] : (m1_connsp_2(sK4(X4),sK1,X4) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v3_pre_topc(sK2,sK1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f7,axiom,(
% 2.17/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.17/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f18,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.17/0.97    inference(ennf_transformation,[],[f7])).
% 2.17/0.97  
% 2.17/0.97  fof(f19,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.97    inference(flattening,[],[f18])).
% 2.17/0.97  
% 2.17/0.97  fof(f28,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.97    inference(nnf_transformation,[],[f19])).
% 2.17/0.97  
% 2.17/0.97  fof(f48,plain,(
% 2.17/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f28])).
% 2.17/0.97  
% 2.17/0.97  fof(f50,plain,(
% 2.17/0.97    ~v2_struct_0(sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f51,plain,(
% 2.17/0.97    v2_pre_topc(sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f37,plain,(
% 2.17/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f25])).
% 2.17/0.97  
% 2.17/0.97  fof(f3,axiom,(
% 2.17/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.17/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f11,plain,(
% 2.17/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.17/0.97    inference(ennf_transformation,[],[f3])).
% 2.17/0.97  
% 2.17/0.97  fof(f12,plain,(
% 2.17/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.17/0.97    inference(flattening,[],[f11])).
% 2.17/0.97  
% 2.17/0.97  fof(f43,plain,(
% 2.17/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f12])).
% 2.17/0.97  
% 2.17/0.97  fof(f56,plain,(
% 2.17/0.97    ( ! [X4] : (r1_tarski(sK4(X4),sK2) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v3_pre_topc(sK2,sK1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f39,plain,(
% 2.17/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f25])).
% 2.17/0.97  
% 2.17/0.97  fof(f4,axiom,(
% 2.17/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.17/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f13,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.97    inference(ennf_transformation,[],[f4])).
% 2.17/0.97  
% 2.17/0.97  fof(f44,plain,(
% 2.17/0.97    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f13])).
% 2.17/0.97  
% 2.17/0.97  fof(f6,axiom,(
% 2.17/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.17/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f16,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.17/0.97    inference(ennf_transformation,[],[f6])).
% 2.17/0.97  
% 2.17/0.97  fof(f17,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.17/0.97    inference(flattening,[],[f16])).
% 2.17/0.97  
% 2.17/0.97  fof(f47,plain,(
% 2.17/0.97    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f17])).
% 2.17/0.97  
% 2.17/0.97  fof(f2,axiom,(
% 2.17/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f26,plain,(
% 2.17/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.97    inference(nnf_transformation,[],[f2])).
% 2.17/0.97  
% 2.17/0.97  fof(f27,plain,(
% 2.17/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.97    inference(flattening,[],[f26])).
% 2.17/0.97  
% 2.17/0.97  fof(f42,plain,(
% 2.17/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f27])).
% 2.17/0.97  
% 2.17/0.97  fof(f46,plain,(
% 2.17/0.97    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f17])).
% 2.17/0.97  
% 2.17/0.97  fof(f59,plain,(
% 2.17/0.97    ( ! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,sK1,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(sK2,sK1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f49,plain,(
% 2.17/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f28])).
% 2.17/0.97  
% 2.17/0.97  fof(f57,plain,(
% 2.17/0.97    m1_subset_1(sK3,u1_struct_0(sK1)) | ~v3_pre_topc(sK2,sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f41,plain,(
% 2.17/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.17/0.97    inference(cnf_transformation,[],[f27])).
% 2.17/0.97  
% 2.17/0.97  fof(f60,plain,(
% 2.17/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.17/0.97    inference(equality_resolution,[],[f41])).
% 2.17/0.97  
% 2.17/0.97  fof(f58,plain,(
% 2.17/0.97    r2_hidden(sK3,sK2) | ~v3_pre_topc(sK2,sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f36])).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1,plain,
% 2.17/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1743,plain,
% 2.17/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.17/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_19,negated_conjecture,
% 2.17/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.17/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1734,plain,
% 2.17/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_18,negated_conjecture,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.17/0.97      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ r2_hidden(X0,sK2) ),
% 2.17/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1735,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.17/0.97      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_8,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ r1_tarski(X0,X2)
% 2.17/0.97      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.17/0.97      | ~ l1_pre_topc(X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_20,negated_conjecture,
% 2.17/0.97      ( l1_pre_topc(sK1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_384,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ r1_tarski(X0,X2)
% 2.17/0.97      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.17/0.97      | sK1 != X1 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_385,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ r1_tarski(X1,X0)
% 2.17/0.97      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_384]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1730,plain,
% 2.17/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.97      | r1_tarski(X1,X0) != iProver_top
% 2.17/0.97      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_17,negated_conjecture,
% 2.17/0.97      ( m1_connsp_2(sK4(X0),sK1,X0)
% 2.17/0.97      | v3_pre_topc(sK2,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.17/0.97      | ~ r2_hidden(X0,sK2) ),
% 2.17/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_12,plain,
% 2.17/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.17/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.17/0.97      | v2_struct_0(X1)
% 2.17/0.97      | ~ v2_pre_topc(X1)
% 2.17/0.97      | ~ l1_pre_topc(X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_22,negated_conjecture,
% 2.17/0.97      ( ~ v2_struct_0(sK1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_246,plain,
% 2.17/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.17/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.17/0.97      | ~ v2_pre_topc(X1)
% 2.17/0.97      | ~ l1_pre_topc(X1)
% 2.17/0.97      | sK1 != X1 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_247,plain,
% 2.17/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.17/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.17/0.97      | ~ v2_pre_topc(sK1)
% 2.17/0.97      | ~ l1_pre_topc(sK1) ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_246]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_21,negated_conjecture,
% 2.17/0.97      ( v2_pre_topc(sK1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_251,plain,
% 2.17/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.17/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_247,c_21,c_20]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_477,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.17/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | r2_hidden(X1,k1_tops_1(sK1,X2))
% 2.17/0.97      | ~ r2_hidden(X0,sK2)
% 2.17/0.97      | X1 != X0
% 2.17/0.97      | sK4(X0) != X2
% 2.17/0.97      | sK1 != sK1 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_251]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_478,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.17/0.97      | ~ m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
% 2.17/0.97      | ~ r2_hidden(X0,sK2) ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_477]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_482,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.17/0.97      | v3_pre_topc(sK2,sK1)
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
% 2.17/0.97      | ~ r2_hidden(X0,sK2) ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_478,c_18]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_483,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
% 2.17/0.97      | ~ r2_hidden(X0,sK2) ),
% 2.17/0.97      inference(renaming,[status(thm)],[c_482]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1724,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2,plain,
% 2.17/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.17/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1742,plain,
% 2.17/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.17/0.97      | r2_hidden(X0,X2) = iProver_top
% 2.17/0.97      | r1_tarski(X1,X2) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2738,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.17/0.97      | r2_hidden(X0,X1) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(k1_tops_1(sK1,sK4(X0)),X1) != iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1724,c_1742]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_6,plain,
% 2.17/0.97      ( m1_subset_1(X0,X1)
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.17/0.97      | ~ r2_hidden(X0,X2) ),
% 2.17/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1739,plain,
% 2.17/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 2.17/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.17/0.97      | r2_hidden(X0,X2) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2652,plain,
% 2.17/0.97      ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1734,c_1739]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_3869,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | r2_hidden(X0,X1) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(k1_tops_1(sK1,sK4(X0)),X1) != iProver_top ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_2738,c_2652]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_3880,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.97      | m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
% 2.17/0.97      | r2_hidden(X1,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(sK4(X1),X0) != iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1730,c_3869]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_4502,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.17/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,X1)) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(sK4(X0),X1) != iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1735,c_3880]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_4640,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,X1)) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(sK4(X0),X1) != iProver_top ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_4502,c_2652]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_4641,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0)) = iProver_top
% 2.17/0.97      | r2_hidden(X1,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(sK4(X1),X0) != iProver_top ),
% 2.17/0.97      inference(renaming,[status(thm)],[c_4640]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_4652,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(sK4(X0),sK2) != iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1734,c_4641]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_16,negated_conjecture,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.17/0.97      | ~ r2_hidden(X0,sK2)
% 2.17/0.97      | r1_tarski(sK4(X0),sK2) ),
% 2.17/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1736,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(sK4(X0),sK2) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2762,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top
% 2.17/0.97      | r1_tarski(sK4(X0),sK2) = iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_2652,c_1736]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_4678,plain,
% 2.17/0.97      ( r2_hidden(X0,sK2) != iProver_top
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
% 2.17/0.97      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_4652,c_2762]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_4679,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
% 2.17/0.97      | r2_hidden(X0,sK2) != iProver_top ),
% 2.17/0.97      inference(renaming,[status(thm)],[c_4678]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_0,plain,
% 2.17/0.97      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1744,plain,
% 2.17/0.97      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.17/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_4687,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),sK2) != iProver_top
% 2.17/0.97      | r1_tarski(X0,k1_tops_1(sK1,sK2)) = iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_4679,c_1744]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_4831,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1743,c_4687]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_26,plain,
% 2.17/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_7,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.17/0.97      | ~ l1_pre_topc(X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_402,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.17/0.97      | sK1 != X1 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_403,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_402]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1896,plain,
% 2.17/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_403]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1897,plain,
% 2.17/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_1896]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_9,plain,
% 2.17/0.97      ( v3_pre_topc(X0,X1)
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.17/0.97      | ~ v2_pre_topc(X1)
% 2.17/0.97      | ~ l1_pre_topc(X1)
% 2.17/0.97      | ~ l1_pre_topc(X3)
% 2.17/0.97      | k1_tops_1(X1,X0) != X0 ),
% 2.17/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_304,plain,
% 2.17/0.97      ( v3_pre_topc(X0,X1)
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.17/0.97      | ~ l1_pre_topc(X1)
% 2.17/0.97      | ~ l1_pre_topc(X3)
% 2.17/0.97      | k1_tops_1(X1,X0) != X0
% 2.17/0.97      | sK1 != X1 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_305,plain,
% 2.17/0.97      ( v3_pre_topc(X0,sK1)
% 2.17/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ l1_pre_topc(X2)
% 2.17/0.97      | ~ l1_pre_topc(sK1)
% 2.17/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_304]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_309,plain,
% 2.17/0.97      ( ~ l1_pre_topc(X2)
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.17/0.97      | v3_pre_topc(X0,sK1)
% 2.17/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_305,c_20]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_310,plain,
% 2.17/0.97      ( v3_pre_topc(X0,sK1)
% 2.17/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ l1_pre_topc(X2)
% 2.17/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 2.17/0.97      inference(renaming,[status(thm)],[c_309]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_414,plain,
% 2.17/0.97      ( v3_pre_topc(X0,sK1)
% 2.17/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | k1_tops_1(sK1,X0) != X0
% 2.17/0.97      | sK1 != X2 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_310]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_415,plain,
% 2.17/0.97      ( v3_pre_topc(X0,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_414]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1367,plain,
% 2.17/0.97      ( v3_pre_topc(X0,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | k1_tops_1(sK1,X0) != X0
% 2.17/0.97      | ~ sP1_iProver_split ),
% 2.17/0.97      inference(splitting,
% 2.17/0.97                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.17/0.97                [c_415]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1368,plain,
% 2.17/0.97      ( sP1_iProver_split | sP0_iProver_split ),
% 2.17/0.97      inference(splitting,
% 2.17/0.97                [splitting(split),new_symbols(definition,[])],
% 2.17/0.97                [c_415]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1366,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ sP0_iProver_split ),
% 2.17/0.97      inference(splitting,
% 2.17/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.17/0.97                [c_415]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1446,plain,
% 2.17/0.97      ( k1_tops_1(sK1,X0) != X0
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | v3_pre_topc(X0,sK1) ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_1367,c_1368,c_1366]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1447,plain,
% 2.17/0.97      ( v3_pre_topc(X0,sK1)
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | k1_tops_1(sK1,X0) != X0 ),
% 2.17/0.97      inference(renaming,[status(thm)],[c_1446]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1899,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1)
% 2.17/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | k1_tops_1(sK1,sK2) != sK2 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_1447]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1900,plain,
% 2.17/0.97      ( k1_tops_1(sK1,sK2) != sK2
% 2.17/0.97      | v3_pre_topc(sK2,sK1) = iProver_top
% 2.17/0.97      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_3,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.17/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1927,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2100,plain,
% 2.17/0.97      ( ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
% 2.17/0.97      | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2))
% 2.17/0.97      | k1_tops_1(sK1,sK2) = sK2 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_1927]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2101,plain,
% 2.17/0.97      ( k1_tops_1(sK1,sK2) = sK2
% 2.17/0.97      | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top
% 2.17/0.97      | r1_tarski(sK2,k1_tops_1(sK1,sK2)) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_2100]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_5022,plain,
% 2.17/0.97      ( v3_pre_topc(sK2,sK1) = iProver_top ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_4831,c_26,c_1897,c_1900,c_2101]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_10,plain,
% 2.17/0.97      ( ~ v3_pre_topc(X0,X1)
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ v2_pre_topc(X3)
% 2.17/0.97      | ~ l1_pre_topc(X3)
% 2.17/0.97      | ~ l1_pre_topc(X1)
% 2.17/0.97      | k1_tops_1(X1,X0) = X0 ),
% 2.17/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_329,plain,
% 2.17/0.97      ( ~ v3_pre_topc(X0,X1)
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.17/0.97      | ~ l1_pre_topc(X1)
% 2.17/0.97      | ~ l1_pre_topc(X3)
% 2.17/0.97      | k1_tops_1(X1,X0) = X0
% 2.17/0.97      | sK1 != X3 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_330,plain,
% 2.17/0.97      ( ~ v3_pre_topc(X0,X1)
% 2.17/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.97      | ~ l1_pre_topc(X1)
% 2.17/0.97      | ~ l1_pre_topc(sK1)
% 2.17/0.97      | k1_tops_1(X1,X0) = X0 ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_329]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_334,plain,
% 2.17/0.98      ( ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.98      | ~ v3_pre_topc(X0,X1)
% 2.17/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_330,c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_335,plain,
% 2.17/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_334]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_366,plain,
% 2.17/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | k1_tops_1(X1,X0) = X0
% 2.17/0.98      | sK1 != X1 ),
% 2.17/0.98      inference(resolution_lifted,[status(thm)],[c_335,c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_367,plain,
% 2.17/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.17/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | k1_tops_1(sK1,X0) = X0 ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_366]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1369,plain,
% 2.17/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | k1_tops_1(sK1,X0) = X0
% 2.17/0.98      | ~ sP2_iProver_split ),
% 2.17/0.98      inference(splitting,
% 2.17/0.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.17/0.98                [c_367]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1732,plain,
% 2.17/0.98      ( k1_tops_1(sK1,X0) = X0
% 2.17/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.98      | sP2_iProver_split != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1370,plain,
% 2.17/0.98      ( sP2_iProver_split | sP0_iProver_split ),
% 2.17/0.98      inference(splitting,
% 2.17/0.98                [splitting(split),new_symbols(definition,[])],
% 2.17/0.98                [c_367]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1399,plain,
% 2.17/0.98      ( sP2_iProver_split = iProver_top
% 2.17/0.98      | sP0_iProver_split = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1370]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1400,plain,
% 2.17/0.98      ( k1_tops_1(sK1,X0) = X0
% 2.17/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.98      | sP2_iProver_split != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1728,plain,
% 2.17/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.98      | sP0_iProver_split != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1366]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1951,plain,
% 2.17/0.98      ( sP0_iProver_split != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1734,c_1728]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2296,plain,
% 2.17/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.17/0.98      | k1_tops_1(sK1,X0) = X0 ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_1732,c_1399,c_1400,c_1951]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2297,plain,
% 2.17/0.98      ( k1_tops_1(sK1,X0) = X0
% 2.17/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_2296]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2304,plain,
% 2.17/0.98      ( k1_tops_1(sK1,sK2) = sK2 | v3_pre_topc(sK2,sK1) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1734,c_2297]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_5027,plain,
% 2.17/0.98      ( k1_tops_1(sK1,sK2) = sK2 ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_5022,c_2304]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_13,negated_conjecture,
% 2.17/0.98      ( ~ m1_connsp_2(X0,sK1,sK3)
% 2.17/0.98      | ~ v3_pre_topc(sK2,sK1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ r1_tarski(X0,sK2) ),
% 2.17/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_11,plain,
% 2.17/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_270,plain,
% 2.17/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.17/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | sK1 != X1 ),
% 2.17/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_271,plain,
% 2.17/0.98      ( m1_connsp_2(X0,sK1,X1)
% 2.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.17/0.98      | ~ v2_pre_topc(sK1)
% 2.17/0.98      | ~ l1_pre_topc(sK1) ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_270]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_275,plain,
% 2.17/0.98      ( m1_connsp_2(X0,sK1,X1)
% 2.17/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_271,c_21,c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_453,plain,
% 2.17/0.98      ( ~ v3_pre_topc(sK2,sK1)
% 2.17/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.17/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ r2_hidden(X0,k1_tops_1(sK1,X2))
% 2.17/0.98      | ~ r1_tarski(X1,sK2)
% 2.17/0.98      | X2 != X1
% 2.17/0.98      | sK3 != X0
% 2.17/0.98      | sK1 != sK1 ),
% 2.17/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_275]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_454,plain,
% 2.17/0.98      ( ~ v3_pre_topc(sK2,sK1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.17/0.98      | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
% 2.17/0.98      | ~ r1_tarski(X0,sK2) ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_453]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_15,negated_conjecture,
% 2.17/0.98      ( ~ v3_pre_topc(sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_458,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ v3_pre_topc(sK2,sK1)
% 2.17/0.98      | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
% 2.17/0.98      | ~ r1_tarski(X0,sK2) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_454,c_15]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_459,plain,
% 2.17/0.98      ( ~ v3_pre_topc(sK2,sK1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.17/0.98      | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
% 2.17/0.98      | ~ r1_tarski(X0,sK2) ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_458]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1725,plain,
% 2.17/0.98      ( v3_pre_topc(sK2,sK1) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.17/0.98      | r2_hidden(sK3,k1_tops_1(sK1,X0)) != iProver_top
% 2.17/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2406,plain,
% 2.17/0.98      ( v3_pre_topc(sK2,sK1) != iProver_top
% 2.17/0.98      | r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top
% 2.17/0.98      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1734,c_1725]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4,plain,
% 2.17/0.98      ( r1_tarski(X0,X0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1968,plain,
% 2.17/0.98      ( r1_tarski(sK2,sK2) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1971,plain,
% 2.17/0.98      ( r1_tarski(sK2,sK2) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1968]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2534,plain,
% 2.17/0.98      ( r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top
% 2.17/0.98      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2406,c_1971]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2535,plain,
% 2.17/0.98      ( v3_pre_topc(sK2,sK1) != iProver_top
% 2.17/0.98      | r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_2534]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_5289,plain,
% 2.17/0.98      ( v3_pre_topc(sK2,sK1) != iProver_top
% 2.17/0.98      | r2_hidden(sK3,sK2) != iProver_top ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_5027,c_2535]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_14,negated_conjecture,
% 2.17/0.98      ( ~ v3_pre_topc(sK2,sK1) | r2_hidden(sK3,sK2) ),
% 2.17/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_37,plain,
% 2.17/0.98      ( v3_pre_topc(sK2,sK1) != iProver_top
% 2.17/0.98      | r2_hidden(sK3,sK2) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(contradiction,plain,
% 2.17/0.98      ( $false ),
% 2.17/0.98      inference(minisat,[status(thm)],[c_5289,c_5022,c_37]) ).
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  ------                               Statistics
% 2.17/0.98  
% 2.17/0.98  ------ General
% 2.17/0.98  
% 2.17/0.98  abstr_ref_over_cycles:                  0
% 2.17/0.98  abstr_ref_under_cycles:                 0
% 2.17/0.98  gc_basic_clause_elim:                   0
% 2.17/0.98  forced_gc_time:                         0
% 2.17/0.98  parsing_time:                           0.008
% 2.17/0.98  unif_index_cands_time:                  0.
% 2.17/0.98  unif_index_add_time:                    0.
% 2.17/0.98  orderings_time:                         0.
% 2.17/0.98  out_proof_time:                         0.011
% 2.17/0.98  total_time:                             0.156
% 2.17/0.98  num_of_symbols:                         50
% 2.17/0.98  num_of_terms:                           3085
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing
% 2.17/0.98  
% 2.17/0.98  num_of_splits:                          4
% 2.17/0.98  num_of_split_atoms:                     3
% 2.17/0.98  num_of_reused_defs:                     1
% 2.17/0.98  num_eq_ax_congr_red:                    11
% 2.17/0.98  num_of_sem_filtered_clauses:            4
% 2.17/0.98  num_of_subtypes:                        0
% 2.17/0.98  monotx_restored_types:                  0
% 2.17/0.98  sat_num_of_epr_types:                   0
% 2.17/0.98  sat_num_of_non_cyclic_types:            0
% 2.17/0.98  sat_guarded_non_collapsed_types:        0
% 2.17/0.98  num_pure_diseq_elim:                    0
% 2.17/0.98  simp_replaced_by:                       0
% 2.17/0.98  res_preprocessed:                       95
% 2.17/0.98  prep_upred:                             0
% 2.17/0.98  prep_unflattend:                        26
% 2.17/0.98  smt_new_axioms:                         0
% 2.17/0.98  pred_elim_cands:                        4
% 2.17/0.98  pred_elim:                              4
% 2.17/0.98  pred_elim_cl:                           5
% 2.17/0.98  pred_elim_cycles:                       6
% 2.17/0.98  merged_defs:                            0
% 2.17/0.98  merged_defs_ncl:                        0
% 2.17/0.98  bin_hyper_res:                          0
% 2.17/0.98  prep_cycles:                            4
% 2.17/0.98  pred_elim_time:                         0.018
% 2.17/0.98  splitting_time:                         0.
% 2.17/0.98  sem_filter_time:                        0.
% 2.17/0.98  monotx_time:                            0.
% 2.17/0.98  subtype_inf_time:                       0.
% 2.17/0.98  
% 2.17/0.98  ------ Problem properties
% 2.17/0.98  
% 2.17/0.98  clauses:                                21
% 2.17/0.98  conjectures:                            5
% 2.17/0.98  epr:                                    6
% 2.17/0.98  horn:                                   15
% 2.17/0.98  ground:                                 5
% 2.17/0.98  unary:                                  2
% 2.17/0.98  binary:                                 9
% 2.17/0.98  lits:                                   57
% 2.17/0.98  lits_eq:                                3
% 2.17/0.98  fd_pure:                                0
% 2.17/0.98  fd_pseudo:                              0
% 2.17/0.98  fd_cond:                                0
% 2.17/0.98  fd_pseudo_cond:                         1
% 2.17/0.98  ac_symbols:                             0
% 2.17/0.98  
% 2.17/0.98  ------ Propositional Solver
% 2.17/0.98  
% 2.17/0.98  prop_solver_calls:                      29
% 2.17/0.98  prop_fast_solver_calls:                 1110
% 2.17/0.98  smt_solver_calls:                       0
% 2.17/0.98  smt_fast_solver_calls:                  0
% 2.17/0.98  prop_num_of_clauses:                    1492
% 2.17/0.98  prop_preprocess_simplified:             4490
% 2.17/0.98  prop_fo_subsumed:                       36
% 2.17/0.98  prop_solver_time:                       0.
% 2.17/0.98  smt_solver_time:                        0.
% 2.17/0.98  smt_fast_solver_time:                   0.
% 2.17/0.98  prop_fast_solver_time:                  0.
% 2.17/0.98  prop_unsat_core_time:                   0.
% 2.17/0.98  
% 2.17/0.98  ------ QBF
% 2.17/0.98  
% 2.17/0.98  qbf_q_res:                              0
% 2.17/0.98  qbf_num_tautologies:                    0
% 2.17/0.98  qbf_prep_cycles:                        0
% 2.17/0.98  
% 2.17/0.98  ------ BMC1
% 2.17/0.98  
% 2.17/0.98  bmc1_current_bound:                     -1
% 2.17/0.98  bmc1_last_solved_bound:                 -1
% 2.17/0.98  bmc1_unsat_core_size:                   -1
% 2.17/0.98  bmc1_unsat_core_parents_size:           -1
% 2.17/0.98  bmc1_merge_next_fun:                    0
% 2.17/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation
% 2.17/0.98  
% 2.17/0.98  inst_num_of_clauses:                    392
% 2.17/0.98  inst_num_in_passive:                    1
% 2.17/0.98  inst_num_in_active:                     233
% 2.17/0.98  inst_num_in_unprocessed:                158
% 2.17/0.98  inst_num_of_loops:                      320
% 2.17/0.98  inst_num_of_learning_restarts:          0
% 2.17/0.98  inst_num_moves_active_passive:          82
% 2.17/0.98  inst_lit_activity:                      0
% 2.17/0.98  inst_lit_activity_moves:                0
% 2.17/0.98  inst_num_tautologies:                   0
% 2.17/0.98  inst_num_prop_implied:                  0
% 2.17/0.98  inst_num_existing_simplified:           0
% 2.17/0.98  inst_num_eq_res_simplified:             0
% 2.17/0.98  inst_num_child_elim:                    0
% 2.17/0.98  inst_num_of_dismatching_blockings:      128
% 2.17/0.98  inst_num_of_non_proper_insts:           529
% 2.17/0.98  inst_num_of_duplicates:                 0
% 2.17/0.98  inst_inst_num_from_inst_to_res:         0
% 2.17/0.98  inst_dismatching_checking_time:         0.
% 2.17/0.98  
% 2.17/0.98  ------ Resolution
% 2.17/0.98  
% 2.17/0.98  res_num_of_clauses:                     0
% 2.17/0.98  res_num_in_passive:                     0
% 2.17/0.98  res_num_in_active:                      0
% 2.17/0.98  res_num_of_loops:                       99
% 2.17/0.98  res_forward_subset_subsumed:            100
% 2.17/0.98  res_backward_subset_subsumed:           0
% 2.17/0.98  res_forward_subsumed:                   0
% 2.17/0.98  res_backward_subsumed:                  0
% 2.17/0.98  res_forward_subsumption_resolution:     0
% 2.17/0.98  res_backward_subsumption_resolution:    0
% 2.17/0.98  res_clause_to_clause_subsumption:       726
% 2.17/0.98  res_orphan_elimination:                 0
% 2.17/0.98  res_tautology_del:                      61
% 2.17/0.98  res_num_eq_res_simplified:              0
% 2.17/0.98  res_num_sel_changes:                    0
% 2.17/0.98  res_moves_from_active_to_pass:          0
% 2.17/0.98  
% 2.17/0.98  ------ Superposition
% 2.17/0.98  
% 2.17/0.98  sup_time_total:                         0.
% 2.17/0.98  sup_time_generating:                    0.
% 2.17/0.98  sup_time_sim_full:                      0.
% 2.17/0.98  sup_time_sim_immed:                     0.
% 2.17/0.98  
% 2.17/0.98  sup_num_of_clauses:                     46
% 2.17/0.98  sup_num_in_active:                      31
% 2.17/0.98  sup_num_in_passive:                     15
% 2.17/0.98  sup_num_of_loops:                       63
% 2.17/0.98  sup_fw_superposition:                   50
% 2.17/0.98  sup_bw_superposition:                   44
% 2.17/0.98  sup_immediate_simplified:               16
% 2.17/0.98  sup_given_eliminated:                   1
% 2.17/0.98  comparisons_done:                       0
% 2.17/0.98  comparisons_avoided:                    0
% 2.17/0.98  
% 2.17/0.98  ------ Simplifications
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  sim_fw_subset_subsumed:                 6
% 2.17/0.98  sim_bw_subset_subsumed:                 34
% 2.17/0.98  sim_fw_subsumed:                        9
% 2.17/0.98  sim_bw_subsumed:                        1
% 2.17/0.98  sim_fw_subsumption_res:                 2
% 2.17/0.98  sim_bw_subsumption_res:                 0
% 2.17/0.98  sim_tautology_del:                      5
% 2.17/0.98  sim_eq_tautology_del:                   5
% 2.17/0.98  sim_eq_res_simp:                        0
% 2.17/0.98  sim_fw_demodulated:                     0
% 2.17/0.98  sim_bw_demodulated:                     9
% 2.17/0.98  sim_light_normalised:                   0
% 2.17/0.98  sim_joinable_taut:                      0
% 2.17/0.98  sim_joinable_simp:                      0
% 2.17/0.98  sim_ac_normalised:                      0
% 2.17/0.98  sim_smt_subsumption:                    0
% 2.17/0.98  
%------------------------------------------------------------------------------
