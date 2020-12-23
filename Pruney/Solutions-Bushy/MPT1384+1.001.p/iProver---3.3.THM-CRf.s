%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1384+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:36 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 699 expanded)
%              Number of clauses        :  134 ( 172 expanded)
%              Number of leaves         :   20 ( 200 expanded)
%              Depth                    :   17
%              Number of atoms          : 1075 (7034 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X2,X3)
              & r1_tarski(X3,X1)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X1)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X2,X3)
                  & r1_tarski(X3,X1)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X1)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X2,X3)
                  & r1_tarski(X3,X1)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X0)
                  | ~ v3_pre_topc(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,X0) )
            & ( ? [X4] :
                  ( r2_hidden(X2,X4)
                  & r1_tarski(X4,X0)
                  & v3_pre_topc(X4,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,X0) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X0)
              | ! [X6] :
                  ( ~ r2_hidden(X5,X6)
                  | ~ r1_tarski(X6,X0)
                  | ~ v3_pre_topc(X6,X1)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
            & ( ? [X7] :
                  ( r2_hidden(X5,X7)
                  & r1_tarski(X7,X0)
                  & v3_pre_topc(X7,X1)
                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X5,X0) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( r2_hidden(X5,X7)
          & r1_tarski(X7,X0)
          & v3_pre_topc(X7,X1)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(X5,sK4(X0,X1,X5))
        & r1_tarski(sK4(X0,X1,X5),X0)
        & v3_pre_topc(sK4(X0,X1,X5),X1)
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X2,X4)
          & r1_tarski(X4,X0)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(X2,sK3(X0,X1))
        & r1_tarski(sK3(X0,X1),X0)
        & v3_pre_topc(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X2,X3)
                | ~ r1_tarski(X3,X0)
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,X0) )
          & ( ? [X4] :
                ( r2_hidden(X2,X4)
                & r1_tarski(X4,X0)
                & v3_pre_topc(X4,X1)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,X0) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(sK2(X0,X1),X3)
              | ~ r1_tarski(X3,X0)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( ? [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              & r1_tarski(X4,X0)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( ~ r2_hidden(sK2(X0,X1),X3)
                | ~ r1_tarski(X3,X0)
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1),X0) )
          & ( ( r2_hidden(sK2(X0,X1),sK3(X0,X1))
              & r1_tarski(sK3(X0,X1),X0)
              & v3_pre_topc(sK3(X0,X1),X1)
              & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1),X0) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X0)
              | ! [X6] :
                  ( ~ r2_hidden(X5,X6)
                  | ~ r1_tarski(X6,X0)
                  | ~ v3_pre_topc(X6,X1)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
            & ( ( r2_hidden(X5,sK4(X0,X1,X5))
                & r1_tarski(sK4(X0,X1,X5),X0)
                & v3_pre_topc(sK4(X0,X1,X5),X1)
                & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X5,X0) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X3)
      | ~ r1_tarski(X3,X0)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

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
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
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
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK5(X0,X1,X2))
        & r1_tarski(sK5(X0,X1,X2),X2)
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK5(X0,X1,X2))
                    & r1_tarski(sK5(X0,X1,X2),X2)
                    & v3_pre_topc(sK5(X0,X1,X2),X0)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK5(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

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
     => ( r1_tarski(sK9(X4),X1)
        & m1_connsp_2(sK9(X4),X0,X4)
        & m1_subset_1(sK9(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
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
            | ~ m1_connsp_2(X3,X0,sK8)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK8,X1)
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
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
                  ( ~ r1_tarski(X3,sK7)
                  | ~ m1_connsp_2(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,sK7)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK7,X0) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( r1_tarski(X5,sK7)
                  & m1_connsp_2(X5,X0,X4)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,sK7)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v3_pre_topc(sK7,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
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
                    | ~ m1_connsp_2(X3,sK6,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK6)) )
            | ~ v3_pre_topc(X1,sK6) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,sK6,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK6))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK6)) )
            | v3_pre_topc(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ( ! [X3] :
            ( ~ r1_tarski(X3,sK7)
            | ~ m1_connsp_2(X3,sK6,sK8)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
        & r2_hidden(sK8,sK7)
        & m1_subset_1(sK8,u1_struct_0(sK6)) )
      | ~ v3_pre_topc(sK7,sK6) )
    & ( ! [X4] :
          ( ( r1_tarski(sK9(X4),sK7)
            & m1_connsp_2(sK9(X4),sK6,X4)
            & m1_subset_1(sK9(X4),k1_zfmisc_1(u1_struct_0(sK6))) )
          | ~ r2_hidden(X4,sK7)
          | ~ m1_subset_1(X4,u1_struct_0(sK6)) )
      | v3_pre_topc(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f46,f50,f49,f48,f47])).

fof(f78,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK5(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK7)
      | ~ m1_connsp_2(X3,sK6,sK8)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ v3_pre_topc(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X4] :
      ( m1_connsp_2(sK9(X4),sK6,X4)
      | ~ r2_hidden(X4,sK7)
      | ~ m1_subset_1(X4,u1_struct_0(sK6))
      | v3_pre_topc(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    ! [X4] :
      ( r1_tarski(sK9(X4),sK7)
      | ~ r2_hidden(X4,sK7)
      | ~ m1_subset_1(X4,u1_struct_0(sK6))
      | v3_pre_topc(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK4(X0,X1,X5))
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( r1_tarski(sK4(X0,X1,X5),X0)
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X0,X5,X1] :
      ( v3_pre_topc(sK4(X0,X1,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v3_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v3_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f30,f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(sK3(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,
    ( r2_hidden(sK8,sK7)
    | ~ v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( sP0(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(sK2(X0,X1),X2)
    | ~ r2_hidden(sK2(X0,X1),X0)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6059,plain,
    ( sP0(X0_49,X0_50)
    | ~ v3_pre_topc(X1_49,X0_50)
    | ~ r2_hidden(sK2(X0_49,X0_50),X1_49)
    | ~ r2_hidden(sK2(X0_49,X0_50),X0_49)
    | ~ r1_tarski(X1_49,X0_49)
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(X0_50))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_9265,plain,
    ( sP0(X0_49,sK6)
    | ~ v3_pre_topc(sK5(sK6,sK2(X1_49,X0_50),X2_49),sK6)
    | ~ r2_hidden(sK2(X0_49,sK6),X0_49)
    | ~ r2_hidden(sK2(X0_49,sK6),sK5(sK6,sK2(X1_49,X0_50),X2_49))
    | ~ r1_tarski(sK5(sK6,sK2(X1_49,X0_50),X2_49),X0_49)
    | ~ m1_subset_1(sK5(sK6,sK2(X1_49,X0_50),X2_49),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6059])).

cnf(c_11573,plain,
    ( sP0(X0_49,sK6)
    | ~ v3_pre_topc(sK5(sK6,sK2(sK7,X0_50),sK9(sK2(sK7,X0_50))),sK6)
    | ~ r2_hidden(sK2(X0_49,sK6),X0_49)
    | ~ r2_hidden(sK2(X0_49,sK6),sK5(sK6,sK2(sK7,X0_50),sK9(sK2(sK7,X0_50))))
    | ~ r1_tarski(sK5(sK6,sK2(sK7,X0_50),sK9(sK2(sK7,X0_50))),X0_49)
    | ~ m1_subset_1(sK5(sK6,sK2(sK7,X0_50),sK9(sK2(sK7,X0_50))),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_9265])).

cnf(c_11575,plain,
    ( sP0(sK7,sK6)
    | ~ v3_pre_topc(sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))),sK6)
    | ~ r2_hidden(sK2(sK7,sK6),sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))))
    | ~ r2_hidden(sK2(sK7,sK6),sK7)
    | ~ r1_tarski(sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))),sK7)
    | ~ m1_subset_1(sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_11573])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6064,plain,
    ( ~ r1_tarski(X0_49,X1_49)
    | ~ r1_tarski(X1_49,X2_49)
    | r1_tarski(X0_49,X2_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_9302,plain,
    ( ~ r1_tarski(X0_49,X1_49)
    | ~ r1_tarski(sK5(sK6,sK2(X2_49,X0_50),X0_49),X0_49)
    | r1_tarski(sK5(sK6,sK2(X2_49,X0_50),X0_49),X1_49) ),
    inference(instantiation,[status(thm)],[c_6064])).

cnf(c_11229,plain,
    ( ~ r1_tarski(sK5(sK6,sK2(X0_49,X0_50),sK9(sK2(sK7,X1_50))),sK9(sK2(sK7,X1_50)))
    | r1_tarski(sK5(sK6,sK2(X0_49,X0_50),sK9(sK2(sK7,X1_50))),sK7)
    | ~ r1_tarski(sK9(sK2(sK7,X1_50)),sK7) ),
    inference(instantiation,[status(thm)],[c_9302])).

cnf(c_11231,plain,
    ( ~ r1_tarski(sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))),sK9(sK2(sK7,sK6)))
    | r1_tarski(sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))),sK7)
    | ~ r1_tarski(sK9(sK2(sK7,sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_11229])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6049,plain,
    ( ~ r2_hidden(X0_49,X1_49)
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(X2_49))
    | ~ v1_xboole_0(X2_49) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_9063,plain,
    ( ~ r2_hidden(sK2(X0_49,X0_50),sK3(X0_49,X0_50))
    | ~ m1_subset_1(sK3(X0_49,X0_50),k1_zfmisc_1(X1_49))
    | ~ v1_xboole_0(X1_49) ),
    inference(instantiation,[status(thm)],[c_6049])).

cnf(c_9065,plain,
    ( ~ r2_hidden(sK2(sK7,sK6),sK3(sK7,sK6))
    | ~ m1_subset_1(sK3(sK7,sK6),k1_zfmisc_1(sK7))
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_9063])).

cnf(c_22,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK5(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_0,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_232,plain,
    ( r2_hidden(X2,sK5(X1,X2,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_0])).

cnf(c_233,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK5(X1,X2,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_556,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | r2_hidden(X1,sK5(sK6,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_233,c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_560,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | r2_hidden(X1,sK5(sK6,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_34,c_33])).

cnf(c_6041,plain,
    ( ~ m1_connsp_2(X0_49,sK6,X1_49)
    | r2_hidden(X1_49,sK5(sK6,X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_560])).

cnf(c_6642,plain,
    ( ~ m1_connsp_2(X0_49,sK6,sK2(X1_49,X0_50))
    | r2_hidden(sK2(X1_49,X0_50),sK5(sK6,sK2(X1_49,X0_50),X0_49))
    | ~ m1_subset_1(sK2(X1_49,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6041])).

cnf(c_8161,plain,
    ( ~ m1_connsp_2(sK9(sK2(sK7,X0_50)),sK6,sK2(sK7,X0_50))
    | r2_hidden(sK2(sK7,X0_50),sK5(sK6,sK2(sK7,X0_50),sK9(sK2(sK7,X0_50))))
    | ~ m1_subset_1(sK2(sK7,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6642])).

cnf(c_8163,plain,
    ( ~ m1_connsp_2(sK9(sK2(sK7,sK6)),sK6,sK2(sK7,sK6))
    | r2_hidden(sK2(sK7,sK6),sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))))
    | ~ m1_subset_1(sK2(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8161])).

cnf(c_23,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK5(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_225,plain,
    ( r1_tarski(sK5(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_0])).

cnf(c_226,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK5(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_225])).

cnf(c_576,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | r1_tarski(sK5(sK6,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_226,c_35])).

cnf(c_580,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | r1_tarski(sK5(sK6,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_34,c_33])).

cnf(c_6040,plain,
    ( ~ m1_connsp_2(X0_49,sK6,X1_49)
    | r1_tarski(sK5(sK6,X1_49,X0_49),X0_49)
    | ~ m1_subset_1(X1_49,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_580])).

cnf(c_6643,plain,
    ( ~ m1_connsp_2(X0_49,sK6,sK2(X1_49,X0_50))
    | r1_tarski(sK5(sK6,sK2(X1_49,X0_50),X0_49),X0_49)
    | ~ m1_subset_1(sK2(X1_49,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6040])).

cnf(c_8135,plain,
    ( ~ m1_connsp_2(sK9(sK2(sK7,X0_50)),sK6,sK2(sK7,X0_50))
    | r1_tarski(sK5(sK6,sK2(sK7,X0_50),sK9(sK2(sK7,X0_50))),sK9(sK2(sK7,X0_50)))
    | ~ m1_subset_1(sK2(sK7,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6643])).

cnf(c_8137,plain,
    ( ~ m1_connsp_2(sK9(sK2(sK7,sK6)),sK6,sK2(sK7,sK6))
    | r1_tarski(sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))),sK9(sK2(sK7,sK6)))
    | ~ m1_subset_1(sK2(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8135])).

cnf(c_25,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_211,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_0])).

cnf(c_616,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK5(sK6,X1,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_211,c_35])).

cnf(c_620,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK5(sK6,X1,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_34,c_33])).

cnf(c_6038,plain,
    ( ~ m1_connsp_2(X0_49,sK6,X1_49)
    | ~ m1_subset_1(X1_49,u1_struct_0(sK6))
    | m1_subset_1(sK5(sK6,X1_49,X0_49),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_6645,plain,
    ( ~ m1_connsp_2(X0_49,sK6,sK2(X1_49,X0_50))
    | m1_subset_1(sK5(sK6,sK2(X1_49,X0_50),X0_49),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(X1_49,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6038])).

cnf(c_8083,plain,
    ( ~ m1_connsp_2(sK9(sK2(sK7,X0_50)),sK6,sK2(sK7,X0_50))
    | m1_subset_1(sK5(sK6,sK2(sK7,X0_50),sK9(sK2(sK7,X0_50))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK7,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6645])).

cnf(c_8085,plain,
    ( ~ m1_connsp_2(sK9(sK2(sK7,sK6)),sK6,sK2(sK7,sK6))
    | m1_subset_1(sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8083])).

cnf(c_24,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK5(X1,X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_218,plain,
    ( v3_pre_topc(sK5(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_0])).

cnf(c_219,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK5(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_596,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | v3_pre_topc(sK5(sK6,X1,X0),sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_219,c_35])).

cnf(c_600,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | v3_pre_topc(sK5(sK6,X1,X0),sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_34,c_33])).

cnf(c_6039,plain,
    ( ~ m1_connsp_2(X0_49,sK6,X1_49)
    | v3_pre_topc(sK5(sK6,X1_49,X0_49),sK6)
    | ~ m1_subset_1(X1_49,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_600])).

cnf(c_6644,plain,
    ( ~ m1_connsp_2(X0_49,sK6,sK2(X1_49,X0_50))
    | v3_pre_topc(sK5(sK6,sK2(X1_49,X0_50),X0_49),sK6)
    | ~ m1_subset_1(sK2(X1_49,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6039])).

cnf(c_8075,plain,
    ( ~ m1_connsp_2(sK9(sK2(sK7,X0_50)),sK6,sK2(sK7,X0_50))
    | v3_pre_topc(sK5(sK6,sK2(sK7,X0_50),sK9(sK2(sK7,X0_50))),sK6)
    | ~ m1_subset_1(sK2(sK7,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6644])).

cnf(c_8077,plain,
    ( ~ m1_connsp_2(sK9(sK2(sK7,sK6)),sK6,sK2(sK7,sK6))
    | v3_pre_topc(sK5(sK6,sK2(sK7,sK6),sK9(sK2(sK7,sK6))),sK6)
    | ~ m1_subset_1(sK2(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8075])).

cnf(c_19,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_670,plain,
    ( m1_connsp_2(X0,sK6,X1)
    | ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_19,c_35])).

cnf(c_674,plain,
    ( m1_connsp_2(X0,sK6,X1)
    | ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_34,c_33])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_690,plain,
    ( m1_connsp_2(X0,sK6,X1)
    | ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_674,c_5])).

cnf(c_6036,plain,
    ( m1_connsp_2(X0_49,sK6,X1_49)
    | ~ v3_pre_topc(X0_49,sK6)
    | ~ r2_hidden(X1_49,X0_49)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_690])).

cnf(c_6377,plain,
    ( m1_connsp_2(X0_49,sK6,sK8)
    | ~ v3_pre_topc(X0_49,sK6)
    | ~ r2_hidden(sK8,X0_49)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6036])).

cnf(c_8007,plain,
    ( m1_connsp_2(sK4(X0_49,sK6,sK8),sK6,sK8)
    | ~ v3_pre_topc(sK4(X0_49,sK6,sK8),sK6)
    | ~ r2_hidden(sK8,sK4(X0_49,sK6,sK8))
    | ~ m1_subset_1(sK4(X0_49,sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6377])).

cnf(c_8014,plain,
    ( m1_connsp_2(sK4(sK7,sK6,sK8),sK6,sK8)
    | ~ v3_pre_topc(sK4(sK7,sK6,sK8),sK6)
    | ~ r2_hidden(sK8,sK4(sK7,sK6,sK8))
    | ~ m1_subset_1(sK4(sK7,sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8007])).

cnf(c_26,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK6,sK8)
    | ~ v3_pre_topc(sK7,sK6)
    | ~ r1_tarski(X0,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6048,negated_conjecture,
    ( ~ m1_connsp_2(X0_49,sK6,sK8)
    | ~ v3_pre_topc(sK7,sK6)
    | ~ r1_tarski(X0_49,sK7)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_7372,plain,
    ( ~ m1_connsp_2(sK4(sK7,X0_50,sK8),sK6,sK8)
    | ~ v3_pre_topc(sK7,sK6)
    | ~ r1_tarski(sK4(sK7,X0_50,sK8),sK7)
    | ~ m1_subset_1(sK4(sK7,X0_50,sK8),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6048])).

cnf(c_7374,plain,
    ( ~ m1_connsp_2(sK4(sK7,sK6,sK8),sK6,sK8)
    | ~ v3_pre_topc(sK7,sK6)
    | ~ r1_tarski(sK4(sK7,sK6,sK8),sK7)
    | ~ m1_subset_1(sK4(sK7,sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_7372])).

cnf(c_6060,plain,
    ( ~ r2_hidden(X0_49,X1_49)
    | m1_subset_1(X0_49,X2_49)
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(X2_49)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_6797,plain,
    ( ~ r2_hidden(sK2(X0_49,X0_50),X1_49)
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(X2_49))
    | m1_subset_1(sK2(X0_49,X0_50),X2_49) ),
    inference(instantiation,[status(thm)],[c_6060])).

cnf(c_7146,plain,
    ( ~ r2_hidden(sK2(X0_49,X0_50),sK3(X1_49,X1_50))
    | ~ m1_subset_1(sK3(X1_49,X1_50),k1_zfmisc_1(X1_49))
    | m1_subset_1(sK2(X0_49,X0_50),X1_49) ),
    inference(instantiation,[status(thm)],[c_6797])).

cnf(c_7148,plain,
    ( ~ r2_hidden(sK2(sK7,sK6),sK3(sK7,sK6))
    | ~ m1_subset_1(sK3(sK7,sK6),k1_zfmisc_1(sK7))
    | m1_subset_1(sK2(sK7,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_7146])).

cnf(c_6975,plain,
    ( ~ r2_hidden(sK2(X0_49,X0_50),sK3(X1_49,X1_50))
    | ~ m1_subset_1(sK3(X1_49,X1_50),k1_zfmisc_1(u1_struct_0(X1_50)))
    | m1_subset_1(sK2(X0_49,X0_50),u1_struct_0(X1_50)) ),
    inference(instantiation,[status(thm)],[c_6797])).

cnf(c_6977,plain,
    ( ~ r2_hidden(sK2(sK7,sK6),sK3(sK7,sK6))
    | ~ m1_subset_1(sK3(sK7,sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK2(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6975])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6062,plain,
    ( ~ r1_tarski(X0_49,X1_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6919,plain,
    ( ~ r1_tarski(sK3(X0_49,X0_50),X0_49)
    | m1_subset_1(sK3(X0_49,X0_50),k1_zfmisc_1(X0_49)) ),
    inference(instantiation,[status(thm)],[c_6062])).

cnf(c_6921,plain,
    ( ~ r1_tarski(sK3(sK7,sK6),sK7)
    | m1_subset_1(sK3(sK7,sK6),k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_6919])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6063,plain,
    ( r2_hidden(X0_49,X1_49)
    | ~ m1_subset_1(X0_49,X1_49)
    | v1_xboole_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_6677,plain,
    ( r2_hidden(sK2(X0_49,X0_50),X1_49)
    | ~ m1_subset_1(sK2(X0_49,X0_50),X1_49)
    | v1_xboole_0(X1_49) ),
    inference(instantiation,[status(thm)],[c_6063])).

cnf(c_6679,plain,
    ( r2_hidden(sK2(sK7,sK6),sK7)
    | ~ m1_subset_1(sK2(sK7,sK6),sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_6677])).

cnf(c_6467,plain,
    ( ~ r2_hidden(sK2(X0_49,X0_50),X0_49)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | m1_subset_1(sK2(X0_49,X0_50),X1_49) ),
    inference(instantiation,[status(thm)],[c_6060])).

cnf(c_6641,plain,
    ( ~ r2_hidden(sK2(X0_49,X0_50),X0_49)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK2(X0_49,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6467])).

cnf(c_6647,plain,
    ( ~ r2_hidden(sK2(sK7,sK6),sK7)
    | m1_subset_1(sK2(sK7,sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6641])).

cnf(c_30,negated_conjecture,
    ( m1_connsp_2(sK9(X0),sK6,X0)
    | v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(X0,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_6044,negated_conjecture,
    ( m1_connsp_2(sK9(X0_49),sK6,X0_49)
    | v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(X0_49,sK7)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_6450,plain,
    ( m1_connsp_2(sK9(sK2(sK7,X0_50)),sK6,sK2(sK7,X0_50))
    | v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(sK2(sK7,X0_50),sK7)
    | ~ m1_subset_1(sK2(sK7,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6044])).

cnf(c_6464,plain,
    ( m1_connsp_2(sK9(sK2(sK7,sK6)),sK6,sK2(sK7,sK6))
    | v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(sK2(sK7,sK6),sK7)
    | ~ m1_subset_1(sK2(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6450])).

cnf(c_29,negated_conjecture,
    ( v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(X0,sK7)
    | r1_tarski(sK9(X0),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6045,negated_conjecture,
    ( v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(X0_49,sK7)
    | r1_tarski(sK9(X0_49),sK7)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_6451,plain,
    ( v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(sK2(sK7,X0_50),sK7)
    | r1_tarski(sK9(sK2(sK7,X0_50)),sK7)
    | ~ m1_subset_1(sK2(sK7,X0_50),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6045])).

cnf(c_6460,plain,
    ( v3_pre_topc(sK7,sK6)
    | ~ r2_hidden(sK2(sK7,sK6),sK7)
    | r1_tarski(sK9(sK2(sK7,sK6)),sK7)
    | ~ m1_subset_1(sK2(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6451])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6053,plain,
    ( ~ sP0(X0_49,X0_50)
    | ~ r2_hidden(X1_49,X0_49)
    | r2_hidden(X1_49,sK4(X0_49,X0_50,X1_49)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_6308,plain,
    ( ~ sP0(sK7,X0_50)
    | r2_hidden(sK8,sK4(sK7,X0_50,sK8))
    | ~ r2_hidden(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_6053])).

cnf(c_6310,plain,
    ( ~ sP0(sK7,sK6)
    | r2_hidden(sK8,sK4(sK7,sK6,sK8))
    | ~ r2_hidden(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_6308])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r1_tarski(sK4(X0,X1,X2),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6052,plain,
    ( ~ sP0(X0_49,X0_50)
    | ~ r2_hidden(X1_49,X0_49)
    | r1_tarski(sK4(X0_49,X0_50,X1_49),X0_49) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_6303,plain,
    ( ~ sP0(sK7,X0_50)
    | ~ r2_hidden(sK8,sK7)
    | r1_tarski(sK4(sK7,X0_50,sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_6052])).

cnf(c_6305,plain,
    ( ~ sP0(sK7,sK6)
    | ~ r2_hidden(sK8,sK7)
    | r1_tarski(sK4(sK7,sK6,sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_6303])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | v3_pre_topc(sK4(X0,X1,X2),X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6051,plain,
    ( ~ sP0(X0_49,X0_50)
    | v3_pre_topc(sK4(X0_49,X0_50,X1_49),X0_50)
    | ~ r2_hidden(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_6298,plain,
    ( ~ sP0(sK7,X0_50)
    | v3_pre_topc(sK4(sK7,X0_50,sK8),X0_50)
    | ~ r2_hidden(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_6051])).

cnf(c_6300,plain,
    ( ~ sP0(sK7,sK6)
    | v3_pre_topc(sK4(sK7,sK6,sK8),sK6)
    | ~ r2_hidden(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_6298])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6050,plain,
    ( ~ sP0(X0_49,X0_50)
    | ~ r2_hidden(X1_49,X0_49)
    | m1_subset_1(sK4(X0_49,X0_50,X1_49),k1_zfmisc_1(u1_struct_0(X0_50))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_6293,plain,
    ( ~ sP0(sK7,X0_50)
    | ~ r2_hidden(sK8,sK7)
    | m1_subset_1(sK4(sK7,X0_50,sK8),k1_zfmisc_1(u1_struct_0(X0_50))) ),
    inference(instantiation,[status(thm)],[c_6050])).

cnf(c_6295,plain,
    ( ~ sP0(sK7,sK6)
    | ~ r2_hidden(sK8,sK7)
    | m1_subset_1(sK4(sK7,sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6293])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v3_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_750,plain,
    ( sP1(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_18,c_33])).

cnf(c_754,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | sP1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_750,c_34])).

cnf(c_755,plain,
    ( sP1(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(renaming,[status(thm)],[c_754])).

cnf(c_784,plain,
    ( ~ sP0(X0,sK6)
    | v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_6,c_755])).

cnf(c_6033,plain,
    ( ~ sP0(X0_49,sK6)
    | v3_pre_topc(X0_49,sK6)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_784])).

cnf(c_6147,plain,
    ( ~ sP0(sK7,sK6)
    | v3_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6033])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v3_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_770,plain,
    ( sP0(X0,sK6)
    | ~ v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_7,c_755])).

cnf(c_6034,plain,
    ( sP0(X0_49,sK6)
    | ~ v3_pre_topc(X0_49,sK6)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_770])).

cnf(c_6144,plain,
    ( sP0(sK7,sK6)
    | ~ v3_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6034])).

cnf(c_12,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6055,plain,
    ( sP0(X0_49,X0_50)
    | r2_hidden(sK2(X0_49,X0_50),X0_49)
    | m1_subset_1(sK3(X0_49,X0_50),k1_zfmisc_1(u1_struct_0(X0_50))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_6091,plain,
    ( sP0(sK7,sK6)
    | r2_hidden(sK2(sK7,sK6),sK7)
    | m1_subset_1(sK3(sK7,sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6055])).

cnf(c_10,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6057,plain,
    ( sP0(X0_49,X0_50)
    | r2_hidden(sK2(X0_49,X0_50),X0_49)
    | r1_tarski(sK3(X0_49,X0_50),X0_49) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_6085,plain,
    ( sP0(sK7,sK6)
    | r2_hidden(sK2(sK7,sK6),sK7)
    | r1_tarski(sK3(sK7,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_6057])).

cnf(c_9,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6058,plain,
    ( sP0(X0_49,X0_50)
    | r2_hidden(sK2(X0_49,X0_50),X0_49)
    | r2_hidden(sK2(X0_49,X0_50),sK3(X0_49,X0_50)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_6082,plain,
    ( sP0(sK7,sK6)
    | r2_hidden(sK2(sK7,sK6),sK3(sK7,sK6))
    | r2_hidden(sK2(sK7,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_6058])).

cnf(c_27,negated_conjecture,
    ( ~ v3_pre_topc(sK7,sK6)
    | r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3010,plain,
    ( ~ sP0(sK7,sK6)
    | r2_hidden(sK8,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_27,c_784])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3012,plain,
    ( r2_hidden(sK8,sK7)
    | ~ sP0(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3010,c_32])).

cnf(c_3013,plain,
    ( ~ sP0(sK7,sK6)
    | r2_hidden(sK8,sK7) ),
    inference(renaming,[status(thm)],[c_3012])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11575,c_11231,c_9065,c_8163,c_8137,c_8085,c_8077,c_8014,c_7374,c_7148,c_6977,c_6921,c_6679,c_6647,c_6464,c_6460,c_6310,c_6305,c_6300,c_6295,c_6147,c_6144,c_6091,c_6085,c_6082,c_3013,c_32])).


%------------------------------------------------------------------------------
