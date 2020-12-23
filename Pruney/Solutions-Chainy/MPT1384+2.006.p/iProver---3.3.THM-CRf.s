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

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :  233 (3303 expanded)
%              Number of clauses        :  160 ( 768 expanded)
%              Number of leaves         :   20 ( 901 expanded)
%              Depth                    :   34
%              Number of atoms          :  931 (30876 expanded)
%              Number of equality atoms :  123 ( 665 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f31])).

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
     => ( r1_tarski(sK4(X4),X1)
        & m1_connsp_2(sK4(X4),X0,X4)
        & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
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
            | ~ m1_connsp_2(X3,X0,sK3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK3,X1)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f46,f45,f44,f43])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ m1_connsp_2(X3,sK1,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f47])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,
    ( r2_hidden(sK3,sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X4] :
      ( m1_connsp_2(sK4(X4),sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X4] :
      ( r1_tarski(sK4(X4),sK2)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1564,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1561,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4714,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1564,c_1561])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6157,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X2,X0) ),
    inference(resolution,[status(thm)],[c_4714,c_3])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2586,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_8,c_23])).

cnf(c_3490,plain,
    ( r1_tarski(X0,u1_struct_0(sK1))
    | ~ r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_6,c_2586])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_454,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_455,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_2574,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1))
    | ~ r1_tarski(X0,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_7,c_455])).

cnf(c_2961,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | r1_tarski(X0,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(X0,u1_struct_0(sK1))
    | ~ r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_2574,c_23])).

cnf(c_3502,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(X0,u1_struct_0(sK1))
    | ~ r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_6,c_2961])).

cnf(c_3912,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3490,c_3502])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_3494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,k1_tops_1(sK1,X1))
    | r1_tarski(X2,k1_tops_1(sK1,X0)) ),
    inference(resolution,[status(thm)],[c_6,c_476])).

cnf(c_4935,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
    inference(resolution,[status(thm)],[c_3494,c_476])).

cnf(c_5088,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | ~ r1_tarski(sK2,X1) ),
    inference(resolution,[status(thm)],[c_4935,c_23])).

cnf(c_2304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5177,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | ~ r1_tarski(sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5088,c_2304,c_3490])).

cnf(c_5178,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0))
    | ~ r1_tarski(sK2,X0) ),
    inference(renaming,[status(thm)],[c_5177])).

cnf(c_21702,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,sK2))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(resolution,[status(thm)],[c_3912,c_5178])).

cnf(c_10,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_433,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_434,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_21889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,sK2))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21702,c_24,c_434])).

cnf(c_22073,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK2))
    | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[status(thm)],[c_21889,c_23])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2081,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2072,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2069,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_2080,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3651,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X2) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2069,c_2080])).

cnf(c_8185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_3651])).

cnf(c_2305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2304])).

cnf(c_3491,plain,
    ( r1_tarski(X0,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3490])).

cnf(c_8895,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8185,c_2305,c_3491])).

cnf(c_8904,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2081,c_8895])).

cnf(c_8963,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8904])).

cnf(c_22078,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22073,c_8963])).

cnf(c_26377,plain,
    ( r2_hidden(k1_tops_1(sK1,X0),X1)
    | ~ r2_hidden(k1_tops_1(sK1,sK2),X1)
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(k1_tops_1(sK1,sK2),k1_tops_1(sK1,X0)) ),
    inference(resolution,[status(thm)],[c_6157,c_22078])).

cnf(c_27447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k1_tops_1(sK1,X0),X1)
    | ~ r2_hidden(k1_tops_1(sK1,sK2),X1)
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[status(thm)],[c_26377,c_5178])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_77,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_81,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_24])).

cnf(c_439,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_438])).

cnf(c_2256,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_2257,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2256])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_2259,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2695,plain,
    ( r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),X0)
    | r1_tarski(X0,k1_tops_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2526,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(k1_tops_1(sK1,sK2),X0)
    | X0 = k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3377,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2))
    | sK2 = k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2526])).

cnf(c_1568,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2426,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
    | X0 != k1_tops_1(sK1,sK2)
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_3387,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
    | v3_pre_topc(sK2,sK1)
    | sK1 != sK1
    | sK2 != k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_3388,plain,
    ( sK1 != sK1
    | sK2 != k1_tops_1(sK1,sK2)
    | v3_pre_topc(k1_tops_1(sK1,sK2),sK1) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3387])).

cnf(c_2706,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_tops_1(sK1,sK2))
    | r1_tarski(X0,k1_tops_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4427,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2706])).

cnf(c_2070,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_3246,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_2070])).

cnf(c_3291,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_3246])).

cnf(c_2298,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2300,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2298])).

cnf(c_3416,plain,
    ( r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3291,c_2300])).

cnf(c_3417,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3416])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2083,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3696,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_2083])).

cnf(c_17,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK1,sK3)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_396,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_397,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_401,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_25,c_24])).

cnf(c_523,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X2))
    | ~ r1_tarski(X1,sK2)
    | X2 != X1
    | sK3 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_401])).

cnf(c_524,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_19,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_19])).

cnf(c_529,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK2) ),
    inference(renaming,[status(thm)],[c_528])).

cnf(c_2067,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK1,X0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_2926,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_2067])).

cnf(c_3126,plain,
    ( r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2926,c_2300])).

cnf(c_3127,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3126])).

cnf(c_5285,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3696,c_3127])).

cnf(c_18,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_41,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5302,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5285,c_41])).

cnf(c_7379,plain,
    ( ~ r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),X0)
    | r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_18709,plain,
    ( ~ r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),X0)
    | r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),sK2)
    | ~ r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_7379])).

cnf(c_22094,plain,
    ( ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | r2_hidden(X0,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(X1,sK2) ),
    inference(resolution,[status(thm)],[c_22078,c_2])).

cnf(c_2336,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
    inference(resolution,[status(thm)],[c_494,c_23])).

cnf(c_3498,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,sK2))
    | r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_6,c_2336])).

cnf(c_2573,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK1))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(resolution,[status(thm)],[c_7,c_494])).

cnf(c_3943,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK2)),sK2)
    | ~ r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_3498,c_2573])).

cnf(c_2683,plain,
    ( ~ r2_hidden(X0,k1_tops_1(sK1,sK2))
    | r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_2,c_2336])).

cnf(c_2839,plain,
    ( r2_hidden(sK0(k1_tops_1(sK1,sK2),X0),sK2)
    | r1_tarski(k1_tops_1(sK1,sK2),X0) ),
    inference(resolution,[status(thm)],[c_2683,c_1])).

cnf(c_2691,plain,
    ( r2_hidden(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_2586,c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2829,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK1)),sK2)
    | r1_tarski(X0,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_2691,c_0])).

cnf(c_3324,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_2839,c_2829])).

cnf(c_10382,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK2)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3943,c_3324])).

cnf(c_3939,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
    inference(resolution,[status(thm)],[c_3498,c_476])).

cnf(c_4534,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3939,c_23,c_2304,c_3490])).

cnf(c_4553,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,X1))
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_4534,c_6])).

cnf(c_8584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X1),sK2) ),
    inference(resolution,[status(thm)],[c_4553,c_476])).

cnf(c_8605,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,X1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8584,c_2304,c_3490])).

cnf(c_8606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
    inference(renaming,[status(thm)],[c_8605])).

cnf(c_2352,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8609,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8606,c_2352,c_4534])).

cnf(c_10407,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,k1_tops_1(sK1,sK2)))
    | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
    inference(resolution,[status(thm)],[c_10382,c_8609])).

cnf(c_10423,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,X0)),sK2)
    | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_10407,c_5178])).

cnf(c_10621,plain,
    ( ~ r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10423,c_23,c_30,c_41,c_77,c_81,c_2257,c_2259,c_3377,c_3388,c_5285])).

cnf(c_3911,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | r1_tarski(X0,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3490,c_2961])).

cnf(c_10633,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[status(thm)],[c_10621,c_3911])).

cnf(c_3309,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | r1_tarski(sK2,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3291])).

cnf(c_11426,plain,
    ( ~ v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10633,c_23,c_30,c_41,c_77,c_81,c_2257,c_2259,c_2298,c_3309,c_3377,c_3388,c_5285])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3735,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_9,c_23])).

cnf(c_21,negated_conjecture,
    ( m1_connsp_2(sK4(X0),sK1,X0)
    | v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_16,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_152,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_153,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_354,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_26])).

cnf(c_355,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_359,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_25,c_24])).

cnf(c_549,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X2))
    | ~ r2_hidden(X0,sK2)
    | X1 != X0
    | sK4(X0) != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_359])).

cnf(c_550,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_3742,plain,
    ( v3_pre_topc(sK2,sK1)
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3735,c_550])).

cnf(c_11465,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
    | ~ r2_hidden(X0,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11426,c_3742])).

cnf(c_22704,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,sK2))
    | ~ r2_hidden(X0,sK2)
    | ~ r1_tarski(sK4(X0),sK2) ),
    inference(resolution,[status(thm)],[c_22094,c_11465])).

cnf(c_2077,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3428,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_2077])).

cnf(c_3452,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3428])).

cnf(c_20,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK2)
    | r1_tarski(sK4(X0),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3743,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ r2_hidden(X0,sK2)
    | r1_tarski(sK4(X0),sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3735,c_20])).

cnf(c_2066,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_9248,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,X1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8904,c_2083])).

cnf(c_10547,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK4(X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2066,c_9248])).

cnf(c_10567,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,sK2))
    | ~ r2_hidden(X0,sK2)
    | ~ r1_tarski(sK4(X0),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10547])).

cnf(c_25025,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(X0,k1_tops_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22704,c_23,c_30,c_41,c_77,c_81,c_2257,c_2259,c_2298,c_3309,c_3377,c_3388,c_3452,c_3743,c_5285,c_10567])).

cnf(c_25026,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,sK2))
    | ~ r2_hidden(X0,sK2) ),
    inference(renaming,[status(thm)],[c_25025])).

cnf(c_25043,plain,
    ( ~ r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),sK2)
    | r1_tarski(X0,k1_tops_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_25026,c_0])).

cnf(c_27804,plain,
    ( ~ r1_tarski(sK2,X0)
    | ~ r1_tarski(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27447,c_23,c_30,c_41,c_77,c_81,c_2257,c_2259,c_2695,c_3377,c_3388,c_4427,c_5285,c_18709,c_25043])).

cnf(c_27805,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(renaming,[status(thm)],[c_27804])).

cnf(c_27822,plain,
    ( ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[status(thm)],[c_27805,c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27822,c_2298])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.27/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.27/1.50  
% 7.27/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.27/1.50  
% 7.27/1.50  ------  iProver source info
% 7.27/1.50  
% 7.27/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.27/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.27/1.50  git: non_committed_changes: false
% 7.27/1.50  git: last_make_outside_of_git: false
% 7.27/1.50  
% 7.27/1.50  ------ 
% 7.27/1.50  ------ Parsing...
% 7.27/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.27/1.50  ------ Proving...
% 7.27/1.50  ------ Problem Properties 
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  clauses                                 20
% 7.27/1.50  conjectures                             5
% 7.27/1.50  EPR                                     5
% 7.27/1.50  Horn                                    16
% 7.27/1.50  unary                                   2
% 7.27/1.50  binary                                  8
% 7.27/1.50  lits                                    55
% 7.27/1.50  lits eq                                 1
% 7.27/1.50  fd_pure                                 0
% 7.27/1.50  fd_pseudo                               0
% 7.27/1.50  fd_cond                                 0
% 7.27/1.50  fd_pseudo_cond                          1
% 7.27/1.50  AC symbols                              0
% 7.27/1.50  
% 7.27/1.50  ------ Input Options Time Limit: Unbounded
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  ------ 
% 7.27/1.50  Current options:
% 7.27/1.50  ------ 
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  ------ Proving...
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  % SZS status Theorem for theBenchmark.p
% 7.27/1.50  
% 7.27/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.27/1.50  
% 7.27/1.50  fof(f2,axiom,(
% 7.27/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f36,plain,(
% 7.27/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.27/1.50    inference(nnf_transformation,[],[f2])).
% 7.27/1.50  
% 7.27/1.50  fof(f37,plain,(
% 7.27/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.27/1.50    inference(flattening,[],[f36])).
% 7.27/1.50  
% 7.27/1.50  fof(f53,plain,(
% 7.27/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f37])).
% 7.27/1.50  
% 7.27/1.50  fof(f3,axiom,(
% 7.27/1.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f15,plain,(
% 7.27/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.27/1.50    inference(ennf_transformation,[],[f3])).
% 7.27/1.50  
% 7.27/1.50  fof(f16,plain,(
% 7.27/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.27/1.50    inference(flattening,[],[f15])).
% 7.27/1.50  
% 7.27/1.50  fof(f54,plain,(
% 7.27/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f16])).
% 7.27/1.50  
% 7.27/1.50  fof(f4,axiom,(
% 7.27/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f38,plain,(
% 7.27/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.27/1.50    inference(nnf_transformation,[],[f4])).
% 7.27/1.50  
% 7.27/1.50  fof(f55,plain,(
% 7.27/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.27/1.50    inference(cnf_transformation,[],[f38])).
% 7.27/1.50  
% 7.27/1.50  fof(f12,conjecture,(
% 7.27/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f13,negated_conjecture,(
% 7.27/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 7.27/1.50    inference(negated_conjecture,[],[f12])).
% 7.27/1.50  
% 7.27/1.50  fof(f30,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f13])).
% 7.27/1.50  
% 7.27/1.50  fof(f31,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.27/1.50    inference(flattening,[],[f30])).
% 7.27/1.50  
% 7.27/1.50  fof(f40,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.27/1.50    inference(nnf_transformation,[],[f31])).
% 7.27/1.50  
% 7.27/1.50  fof(f41,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.27/1.50    inference(flattening,[],[f40])).
% 7.27/1.50  
% 7.27/1.50  fof(f42,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.27/1.50    inference(rectify,[],[f41])).
% 7.27/1.50  
% 7.27/1.50  fof(f46,plain,(
% 7.27/1.50    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK4(X4),X1) & m1_connsp_2(sK4(X4),X0,X4) & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f45,plain,(
% 7.27/1.50    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK3,X1) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f44,plain,(
% 7.27/1.50    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK2,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK2) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f43,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK1,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f47,plain,(
% 7.27/1.50    (((! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,sK1,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & r2_hidden(sK3,sK2) & m1_subset_1(sK3,u1_struct_0(sK1))) | ~v3_pre_topc(sK2,sK1)) & (! [X4] : ((r1_tarski(sK4(X4),sK2) & m1_connsp_2(sK4(X4),sK1,X4) & m1_subset_1(sK4(X4),k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.27/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f46,f45,f44,f43])).
% 7.27/1.50  
% 7.27/1.50  fof(f68,plain,(
% 7.27/1.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  fof(f56,plain,(
% 7.27/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f38])).
% 7.27/1.50  
% 7.27/1.50  fof(f9,axiom,(
% 7.27/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f24,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(ennf_transformation,[],[f9])).
% 7.27/1.50  
% 7.27/1.50  fof(f25,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(flattening,[],[f24])).
% 7.27/1.50  
% 7.27/1.50  fof(f61,plain,(
% 7.27/1.50    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f25])).
% 7.27/1.50  
% 7.27/1.50  fof(f67,plain,(
% 7.27/1.50    l1_pre_topc(sK1)),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  fof(f8,axiom,(
% 7.27/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f22,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(ennf_transformation,[],[f8])).
% 7.27/1.50  
% 7.27/1.50  fof(f23,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(flattening,[],[f22])).
% 7.27/1.50  
% 7.27/1.50  fof(f60,plain,(
% 7.27/1.50    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f23])).
% 7.27/1.50  
% 7.27/1.50  fof(f6,axiom,(
% 7.27/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f19,plain,(
% 7.27/1.50    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f6])).
% 7.27/1.50  
% 7.27/1.50  fof(f20,plain,(
% 7.27/1.50    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.27/1.50    inference(flattening,[],[f19])).
% 7.27/1.50  
% 7.27/1.50  fof(f58,plain,(
% 7.27/1.50    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f20])).
% 7.27/1.50  
% 7.27/1.50  fof(f66,plain,(
% 7.27/1.50    v2_pre_topc(sK1)),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  fof(f51,plain,(
% 7.27/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.27/1.50    inference(cnf_transformation,[],[f37])).
% 7.27/1.50  
% 7.27/1.50  fof(f76,plain,(
% 7.27/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.27/1.50    inference(equality_resolution,[],[f51])).
% 7.27/1.50  
% 7.27/1.50  fof(f7,axiom,(
% 7.27/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f21,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(ennf_transformation,[],[f7])).
% 7.27/1.50  
% 7.27/1.50  fof(f59,plain,(
% 7.27/1.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f21])).
% 7.27/1.50  
% 7.27/1.50  fof(f1,axiom,(
% 7.27/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f14,plain,(
% 7.27/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f1])).
% 7.27/1.50  
% 7.27/1.50  fof(f32,plain,(
% 7.27/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.27/1.50    inference(nnf_transformation,[],[f14])).
% 7.27/1.50  
% 7.27/1.50  fof(f33,plain,(
% 7.27/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.27/1.50    inference(rectify,[],[f32])).
% 7.27/1.50  
% 7.27/1.50  fof(f34,plain,(
% 7.27/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f35,plain,(
% 7.27/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.27/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 7.27/1.50  
% 7.27/1.50  fof(f49,plain,(
% 7.27/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f35])).
% 7.27/1.50  
% 7.27/1.50  fof(f48,plain,(
% 7.27/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f35])).
% 7.27/1.50  
% 7.27/1.50  fof(f74,plain,(
% 7.27/1.50    ( ! [X3] : (~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,sK1,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(sK2,sK1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  fof(f10,axiom,(
% 7.27/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f26,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f10])).
% 7.27/1.50  
% 7.27/1.50  fof(f27,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.27/1.50    inference(flattening,[],[f26])).
% 7.27/1.50  
% 7.27/1.50  fof(f39,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.27/1.50    inference(nnf_transformation,[],[f27])).
% 7.27/1.50  
% 7.27/1.50  fof(f63,plain,(
% 7.27/1.50    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f39])).
% 7.27/1.50  
% 7.27/1.50  fof(f65,plain,(
% 7.27/1.50    ~v2_struct_0(sK1)),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  fof(f72,plain,(
% 7.27/1.50    m1_subset_1(sK3,u1_struct_0(sK1)) | ~v3_pre_topc(sK2,sK1)),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  fof(f73,plain,(
% 7.27/1.50    r2_hidden(sK3,sK2) | ~v3_pre_topc(sK2,sK1)),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  fof(f50,plain,(
% 7.27/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f35])).
% 7.27/1.50  
% 7.27/1.50  fof(f5,axiom,(
% 7.27/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f17,plain,(
% 7.27/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.27/1.50    inference(ennf_transformation,[],[f5])).
% 7.27/1.50  
% 7.27/1.50  fof(f18,plain,(
% 7.27/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.27/1.50    inference(flattening,[],[f17])).
% 7.27/1.50  
% 7.27/1.50  fof(f57,plain,(
% 7.27/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f18])).
% 7.27/1.50  
% 7.27/1.50  fof(f70,plain,(
% 7.27/1.50    ( ! [X4] : (m1_connsp_2(sK4(X4),sK1,X4) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v3_pre_topc(sK2,sK1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  fof(f62,plain,(
% 7.27/1.50    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f39])).
% 7.27/1.50  
% 7.27/1.50  fof(f11,axiom,(
% 7.27/1.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.27/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f28,plain,(
% 7.27/1.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f11])).
% 7.27/1.50  
% 7.27/1.50  fof(f29,plain,(
% 7.27/1.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.27/1.50    inference(flattening,[],[f28])).
% 7.27/1.50  
% 7.27/1.50  fof(f64,plain,(
% 7.27/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f29])).
% 7.27/1.50  
% 7.27/1.50  fof(f71,plain,(
% 7.27/1.50    ( ! [X4] : (r1_tarski(sK4(X4),sK2) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v3_pre_topc(sK2,sK1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f47])).
% 7.27/1.50  
% 7.27/1.50  cnf(c_1564,plain,
% 7.27/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.27/1.50      theory(equality) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_1561,plain,( X0 = X0 ),theory(equality) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_4714,plain,
% 7.27/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_1564,c_1561]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.27/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_6157,plain,
% 7.27/1.50      ( ~ r2_hidden(X0,X1)
% 7.27/1.50      | r2_hidden(X2,X1)
% 7.27/1.50      | ~ r1_tarski(X0,X2)
% 7.27/1.50      | ~ r1_tarski(X2,X0) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_4714,c_3]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_6,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.27/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_8,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_23,negated_conjecture,
% 7.27/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.27/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2586,plain,
% 7.27/1.50      ( r1_tarski(sK2,u1_struct_0(sK1)) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_8,c_23]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3490,plain,
% 7.27/1.50      ( r1_tarski(X0,u1_struct_0(sK1)) | ~ r1_tarski(X0,sK2) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_6,c_2586]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_7,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_13,plain,
% 7.27/1.50      ( ~ v3_pre_topc(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ r1_tarski(X0,X2)
% 7.27/1.50      | r1_tarski(X0,k1_tops_1(X1,X2))
% 7.27/1.50      | ~ l1_pre_topc(X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_24,negated_conjecture,
% 7.27/1.50      ( l1_pre_topc(sK1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_454,plain,
% 7.27/1.50      ( ~ v3_pre_topc(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ r1_tarski(X0,X2)
% 7.27/1.50      | r1_tarski(X0,k1_tops_1(X1,X2))
% 7.27/1.50      | sK1 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_455,plain,
% 7.27/1.50      ( ~ v3_pre_topc(X0,sK1)
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X0,X1)
% 7.27/1.50      | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_454]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2574,plain,
% 7.27/1.50      ( ~ v3_pre_topc(X0,sK1)
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X0,X1)
% 7.27/1.50      | r1_tarski(X0,k1_tops_1(sK1,X1))
% 7.27/1.50      | ~ r1_tarski(X0,u1_struct_0(sK1)) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_7,c_455]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2961,plain,
% 7.27/1.50      ( ~ v3_pre_topc(X0,sK1)
% 7.27/1.50      | r1_tarski(X0,k1_tops_1(sK1,sK2))
% 7.27/1.50      | ~ r1_tarski(X0,u1_struct_0(sK1))
% 7.27/1.50      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_2574,c_23]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3502,plain,
% 7.27/1.50      ( ~ v3_pre_topc(X0,sK1)
% 7.27/1.50      | ~ r1_tarski(X1,X0)
% 7.27/1.50      | r1_tarski(X1,k1_tops_1(sK1,sK2))
% 7.27/1.50      | ~ r1_tarski(X0,u1_struct_0(sK1))
% 7.27/1.50      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_6,c_2961]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3912,plain,
% 7.27/1.50      ( ~ v3_pre_topc(X0,sK1)
% 7.27/1.50      | ~ r1_tarski(X1,X0)
% 7.27/1.50      | r1_tarski(X1,k1_tops_1(sK1,sK2))
% 7.27/1.50      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.50      inference(backward_subsumption_resolution,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_3490,c_3502]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_12,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ r1_tarski(X0,X2)
% 7.27/1.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.27/1.50      | ~ l1_pre_topc(X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_475,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ r1_tarski(X0,X2)
% 7.27/1.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.27/1.50      | sK1 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_476,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X1,X0)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_475]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3494,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X1,X0)
% 7.27/1.50      | ~ r1_tarski(X2,k1_tops_1(sK1,X1))
% 7.27/1.50      | r1_tarski(X2,k1_tops_1(sK1,X0)) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_6,c_476]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_4935,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X2,X1)
% 7.27/1.50      | ~ r1_tarski(X0,X2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_3494,c_476]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_5088,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X0,sK2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 7.27/1.50      | ~ r1_tarski(sK2,X1) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_4935,c_23]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2304,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X0,u1_struct_0(sK1)) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_5177,plain,
% 7.27/1.50      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X0,sK2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 7.27/1.50      | ~ r1_tarski(sK2,X1) ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_5088,c_2304,c_3490]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_5178,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X1,sK2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0))
% 7.27/1.50      | ~ r1_tarski(sK2,X0) ),
% 7.27/1.50      inference(renaming,[status(thm)],[c_5177]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21702,plain,
% 7.27/1.50      ( ~ v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X1,sK2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,sK2))
% 7.27/1.50      | ~ r1_tarski(k1_tops_1(sK1,X0),sK2)
% 7.27/1.50      | ~ r1_tarski(sK2,X0) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_3912,c_5178]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_10,plain,
% 7.27/1.50      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.27/1.50      | ~ v2_pre_topc(X0)
% 7.27/1.50      | ~ l1_pre_topc(X0) ),
% 7.27/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_25,negated_conjecture,
% 7.27/1.50      ( v2_pre_topc(sK1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_433,plain,
% 7.27/1.50      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.27/1.50      | ~ l1_pre_topc(X0)
% 7.27/1.50      | sK1 != X0 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_434,plain,
% 7.27/1.50      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ l1_pre_topc(sK1) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_433]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21889,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | ~ r1_tarski(X1,sK2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,sK2))
% 7.27/1.50      | ~ r1_tarski(k1_tops_1(sK1,X0),sK2)
% 7.27/1.50      | ~ r1_tarski(sK2,X0) ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_21702,c_24,c_434]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_22073,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,sK2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK2))
% 7.27/1.50      | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
% 7.27/1.50      | ~ r1_tarski(sK2,sK2) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_21889,c_23]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_5,plain,
% 7.27/1.50      ( r1_tarski(X0,X0) ),
% 7.27/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2081,plain,
% 7.27/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2072,plain,
% 7.27/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2069,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2080,plain,
% 7.27/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.27/1.50      | r1_tarski(X1,X2) != iProver_top
% 7.27/1.50      | r1_tarski(X0,X2) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3651,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),X2) != iProver_top
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X1),X2) = iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2069,c_2080]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_8185,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.50      | r1_tarski(X0,sK2) != iProver_top
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),X1) = iProver_top
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,sK2),X1) != iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2072,c_3651]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2305,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.27/1.50      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_2304]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3491,plain,
% 7.27/1.50      ( r1_tarski(X0,u1_struct_0(sK1)) = iProver_top
% 7.27/1.50      | r1_tarski(X0,sK2) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_3490]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_8895,plain,
% 7.27/1.50      ( r1_tarski(X0,sK2) != iProver_top
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),X1) = iProver_top
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,sK2),X1) != iProver_top ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_8185,c_2305,c_3491]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_8904,plain,
% 7.27/1.50      ( r1_tarski(X0,sK2) != iProver_top
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK2)) = iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2081,c_8895]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_8963,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,sK2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK2)) ),
% 7.27/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_8904]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_22078,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,sK2)
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,sK2)) ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_22073,c_8963]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_26377,plain,
% 7.27/1.50      ( r2_hidden(k1_tops_1(sK1,X0),X1)
% 7.27/1.50      | ~ r2_hidden(k1_tops_1(sK1,sK2),X1)
% 7.27/1.50      | ~ r1_tarski(X0,sK2)
% 7.27/1.50      | ~ r1_tarski(k1_tops_1(sK1,sK2),k1_tops_1(sK1,X0)) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_6157,c_22078]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_27447,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | r2_hidden(k1_tops_1(sK1,X0),X1)
% 7.27/1.50      | ~ r2_hidden(k1_tops_1(sK1,sK2),X1)
% 7.27/1.50      | ~ r1_tarski(X0,sK2)
% 7.27/1.50      | ~ r1_tarski(sK2,X0)
% 7.27/1.50      | ~ r1_tarski(sK2,sK2) ),
% 7.27/1.50      inference(resolution,[status(thm)],[c_26377,c_5178]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_30,plain,
% 7.27/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_77,plain,
% 7.27/1.50      ( r1_tarski(sK1,sK1) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_81,plain,
% 7.27/1.50      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_438,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_434,c_24]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_439,plain,
% 7.27/1.50      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.27/1.50      inference(renaming,[status(thm)],[c_438]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2256,plain,
% 7.27/1.50      ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
% 7.27/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_439]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2257,plain,
% 7.27/1.50      ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1) = iProver_top
% 7.27/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_2256]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_11,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.27/1.50      | ~ l1_pre_topc(X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_493,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.27/1.50      | sK1 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_494,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_493]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2259,plain,
% 7.27/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.50      | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_494]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_1,plain,
% 7.27/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2695,plain,
% 7.27/1.50      ( r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),X0)
% 7.27/1.50      | r1_tarski(X0,k1_tops_1(sK1,sK2)) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2526,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,k1_tops_1(sK1,sK2))
% 7.27/1.50      | ~ r1_tarski(k1_tops_1(sK1,sK2),X0)
% 7.27/1.51      | X0 = k1_tops_1(sK1,sK2) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3377,plain,
% 7.27/1.51      ( ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
% 7.27/1.51      | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2))
% 7.27/1.51      | sK2 = k1_tops_1(sK1,sK2) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_2526]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_1568,plain,
% 7.27/1.51      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.27/1.51      theory(equality) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2426,plain,
% 7.27/1.51      ( v3_pre_topc(X0,X1)
% 7.27/1.51      | ~ v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
% 7.27/1.51      | X0 != k1_tops_1(sK1,sK2)
% 7.27/1.51      | X1 != sK1 ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_1568]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3387,plain,
% 7.27/1.51      ( ~ v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
% 7.27/1.51      | v3_pre_topc(sK2,sK1)
% 7.27/1.51      | sK1 != sK1
% 7.27/1.51      | sK2 != k1_tops_1(sK1,sK2) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_2426]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3388,plain,
% 7.27/1.51      ( sK1 != sK1
% 7.27/1.51      | sK2 != k1_tops_1(sK1,sK2)
% 7.27/1.51      | v3_pre_topc(k1_tops_1(sK1,sK2),sK1) != iProver_top
% 7.27/1.51      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 7.27/1.51      inference(predicate_to_equality,[status(thm)],[c_3387]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2706,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,X1)
% 7.27/1.51      | ~ r1_tarski(X1,k1_tops_1(sK1,sK2))
% 7.27/1.51      | r1_tarski(X0,k1_tops_1(sK1,sK2)) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_4427,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,k1_tops_1(sK1,sK2))
% 7.27/1.51      | ~ r1_tarski(sK2,X0)
% 7.27/1.51      | r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_2706]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2070,plain,
% 7.27/1.51      ( v3_pre_topc(X0,sK1) != iProver_top
% 7.27/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.27/1.51      | r1_tarski(X0,k1_tops_1(sK1,X1)) = iProver_top ),
% 7.27/1.51      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3246,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.51      | r1_tarski(sK2,X0) != iProver_top
% 7.27/1.51      | r1_tarski(sK2,k1_tops_1(sK1,X0)) = iProver_top ),
% 7.27/1.51      inference(superposition,[status(thm)],[c_2072,c_2070]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3291,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top
% 7.27/1.51      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.27/1.51      inference(superposition,[status(thm)],[c_2072,c_3246]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2298,plain,
% 7.27/1.51      ( r1_tarski(sK2,sK2) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2300,plain,
% 7.27/1.51      ( r1_tarski(sK2,sK2) = iProver_top ),
% 7.27/1.51      inference(predicate_to_equality,[status(thm)],[c_2298]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3416,plain,
% 7.27/1.51      ( r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top
% 7.27/1.51      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_3291,c_2300]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3417,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top ),
% 7.27/1.51      inference(renaming,[status(thm)],[c_3416]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2,plain,
% 7.27/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.27/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2083,plain,
% 7.27/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.27/1.51      | r2_hidden(X0,X2) = iProver_top
% 7.27/1.51      | r1_tarski(X1,X2) != iProver_top ),
% 7.27/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3696,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
% 7.27/1.51      | r2_hidden(X0,sK2) != iProver_top ),
% 7.27/1.51      inference(superposition,[status(thm)],[c_3417,c_2083]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_17,negated_conjecture,
% 7.27/1.51      ( ~ m1_connsp_2(X0,sK1,sK3)
% 7.27/1.51      | ~ v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_14,plain,
% 7.27/1.51      ( m1_connsp_2(X0,X1,X2)
% 7.27/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.27/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.51      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 7.27/1.51      | v2_struct_0(X1)
% 7.27/1.51      | ~ v2_pre_topc(X1)
% 7.27/1.51      | ~ l1_pre_topc(X1) ),
% 7.27/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_26,negated_conjecture,
% 7.27/1.51      ( ~ v2_struct_0(sK1) ),
% 7.27/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_396,plain,
% 7.27/1.51      ( m1_connsp_2(X0,X1,X2)
% 7.27/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.27/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.51      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 7.27/1.51      | ~ v2_pre_topc(X1)
% 7.27/1.51      | ~ l1_pre_topc(X1)
% 7.27/1.51      | sK1 != X1 ),
% 7.27/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_397,plain,
% 7.27/1.51      ( m1_connsp_2(X0,sK1,X1)
% 7.27/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.27/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 7.27/1.51      | ~ v2_pre_topc(sK1)
% 7.27/1.51      | ~ l1_pre_topc(sK1) ),
% 7.27/1.51      inference(unflattening,[status(thm)],[c_396]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_401,plain,
% 7.27/1.51      ( m1_connsp_2(X0,sK1,X1)
% 7.27/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.27/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_397,c_25,c_24]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_523,plain,
% 7.27/1.51      ( ~ v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.27/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r2_hidden(X0,k1_tops_1(sK1,X2))
% 7.27/1.51      | ~ r1_tarski(X1,sK2)
% 7.27/1.51      | X2 != X1
% 7.27/1.51      | sK3 != X0
% 7.27/1.51      | sK1 != sK1 ),
% 7.27/1.51      inference(resolution_lifted,[status(thm)],[c_17,c_401]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_524,plain,
% 7.27/1.51      ( ~ v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 7.27/1.51      | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
% 7.27/1.51      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(unflattening,[status(thm)],[c_523]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_19,negated_conjecture,
% 7.27/1.51      ( ~ v3_pre_topc(sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 7.27/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_528,plain,
% 7.27/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
% 7.27/1.51      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_524,c_19]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_529,plain,
% 7.27/1.51      ( ~ v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r2_hidden(sK3,k1_tops_1(sK1,X0))
% 7.27/1.51      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(renaming,[status(thm)],[c_528]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2067,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.27/1.51      | r2_hidden(sK3,k1_tops_1(sK1,X0)) != iProver_top
% 7.27/1.51      | r1_tarski(X0,sK2) != iProver_top ),
% 7.27/1.51      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2926,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top
% 7.27/1.51      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.27/1.51      inference(superposition,[status(thm)],[c_2072,c_2067]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3126,plain,
% 7.27/1.51      ( r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top
% 7.27/1.51      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_2926,c_2300]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3127,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | r2_hidden(sK3,k1_tops_1(sK1,sK2)) != iProver_top ),
% 7.27/1.51      inference(renaming,[status(thm)],[c_3126]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_5285,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | r2_hidden(sK3,sK2) != iProver_top ),
% 7.27/1.51      inference(superposition,[status(thm)],[c_3696,c_3127]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_18,negated_conjecture,
% 7.27/1.51      ( ~ v3_pre_topc(sK2,sK1) | r2_hidden(sK3,sK2) ),
% 7.27/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_41,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top
% 7.27/1.51      | r2_hidden(sK3,sK2) = iProver_top ),
% 7.27/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_5302,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) != iProver_top ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_5285,c_41]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_7379,plain,
% 7.27/1.51      ( ~ r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),X0)
% 7.27/1.51      | r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),X1)
% 7.27/1.51      | ~ r1_tarski(X0,X1) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_18709,plain,
% 7.27/1.51      ( ~ r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),X0)
% 7.27/1.51      | r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),sK2)
% 7.27/1.51      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_7379]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_22094,plain,
% 7.27/1.51      ( ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 7.27/1.51      | r2_hidden(X0,k1_tops_1(sK1,sK2))
% 7.27/1.51      | ~ r1_tarski(X1,sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_22078,c_2]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2336,plain,
% 7.27/1.51      ( r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_494,c_23]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3498,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,k1_tops_1(sK1,sK2)) | r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_6,c_2336]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2573,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,u1_struct_0(sK1))
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_7,c_494]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3943,plain,
% 7.27/1.51      ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK2)),sK2)
% 7.27/1.51      | ~ r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_3498,c_2573]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2683,plain,
% 7.27/1.51      ( ~ r2_hidden(X0,k1_tops_1(sK1,sK2)) | r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_2,c_2336]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2839,plain,
% 7.27/1.51      ( r2_hidden(sK0(k1_tops_1(sK1,sK2),X0),sK2)
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,sK2),X0) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_2683,c_1]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2691,plain,
% 7.27/1.51      ( r2_hidden(X0,u1_struct_0(sK1)) | ~ r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_2586,c_2]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_0,plain,
% 7.27/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.27/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2829,plain,
% 7.27/1.51      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK1)),sK2)
% 7.27/1.51      | r1_tarski(X0,u1_struct_0(sK1)) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_2691,c_0]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3324,plain,
% 7.27/1.51      ( r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_2839,c_2829]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_10382,plain,
% 7.27/1.51      ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK2)),sK2) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_3943,c_3324]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3939,plain,
% 7.27/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r1_tarski(X0,sK2)
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_3498,c_476]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_4534,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,sK2) | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_3939,c_23,c_2304,c_3490]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_4553,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,k1_tops_1(sK1,X1))
% 7.27/1.51      | ~ r1_tarski(X1,sK2)
% 7.27/1.51      | r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_4534,c_6]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_8584,plain,
% 7.27/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r1_tarski(X1,X0)
% 7.27/1.51      | ~ r1_tarski(X0,sK2)
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,X1),sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_4553,c_476]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_8605,plain,
% 7.27/1.51      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r1_tarski(X1,X0)
% 7.27/1.51      | ~ r1_tarski(X0,sK2)
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,X1),sK2) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_8584,c_2304,c_3490]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_8606,plain,
% 7.27/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r1_tarski(X0,X1)
% 7.27/1.51      | ~ r1_tarski(X1,sK2)
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
% 7.27/1.51      inference(renaming,[status(thm)],[c_8605]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2352,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK2) | r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_8609,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,X1)
% 7.27/1.51      | ~ r1_tarski(X1,sK2)
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_8606,c_2352,c_4534]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_10407,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,k1_tops_1(sK1,k1_tops_1(sK1,sK2)))
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,X0),sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_10382,c_8609]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_10423,plain,
% 7.27/1.51      ( ~ m1_subset_1(k1_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.27/1.51      | ~ r1_tarski(X0,sK2)
% 7.27/1.51      | r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,X0)),sK2)
% 7.27/1.51      | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_10407,c_5178]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_10621,plain,
% 7.27/1.51      ( ~ r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_10423,c_23,c_30,c_41,c_77,c_81,c_2257,c_2259,c_3377,
% 7.27/1.51                 c_3388,c_5285]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3911,plain,
% 7.27/1.51      ( ~ v3_pre_topc(X0,sK1)
% 7.27/1.51      | r1_tarski(X0,k1_tops_1(sK1,sK2))
% 7.27/1.51      | ~ r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(backward_subsumption_resolution,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_3490,c_2961]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_10633,plain,
% 7.27/1.51      ( ~ v3_pre_topc(sK2,sK1) | ~ r1_tarski(sK2,sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_10621,c_3911]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3309,plain,
% 7.27/1.51      ( ~ v3_pre_topc(sK2,sK1)
% 7.27/1.51      | r1_tarski(sK2,k1_tops_1(sK1,sK2))
% 7.27/1.51      | ~ r1_tarski(sK2,sK2) ),
% 7.27/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3291]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_11426,plain,
% 7.27/1.51      ( ~ v3_pre_topc(sK2,sK1) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_10633,c_23,c_30,c_41,c_77,c_81,c_2257,c_2259,c_2298,
% 7.27/1.51                 c_3309,c_3377,c_3388,c_5285]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_9,plain,
% 7.27/1.51      ( m1_subset_1(X0,X1)
% 7.27/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.27/1.51      | ~ r2_hidden(X0,X2) ),
% 7.27/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3735,plain,
% 7.27/1.51      ( m1_subset_1(X0,u1_struct_0(sK1)) | ~ r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_9,c_23]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_21,negated_conjecture,
% 7.27/1.51      ( m1_connsp_2(sK4(X0),sK1,X0)
% 7.27/1.51      | v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.27/1.51      | ~ r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_15,plain,
% 7.27/1.51      ( ~ m1_connsp_2(X0,X1,X2)
% 7.27/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.27/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.51      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.27/1.51      | v2_struct_0(X1)
% 7.27/1.51      | ~ v2_pre_topc(X1)
% 7.27/1.51      | ~ l1_pre_topc(X1) ),
% 7.27/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_16,plain,
% 7.27/1.51      ( ~ m1_connsp_2(X0,X1,X2)
% 7.27/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.27/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.51      | v2_struct_0(X1)
% 7.27/1.51      | ~ v2_pre_topc(X1)
% 7.27/1.51      | ~ l1_pre_topc(X1) ),
% 7.27/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_152,plain,
% 7.27/1.51      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.27/1.51      | ~ m1_connsp_2(X0,X1,X2)
% 7.27/1.51      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.27/1.51      | v2_struct_0(X1)
% 7.27/1.51      | ~ v2_pre_topc(X1)
% 7.27/1.51      | ~ l1_pre_topc(X1) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_15,c_16]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_153,plain,
% 7.27/1.51      ( ~ m1_connsp_2(X0,X1,X2)
% 7.27/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.27/1.51      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.27/1.51      | v2_struct_0(X1)
% 7.27/1.51      | ~ v2_pre_topc(X1)
% 7.27/1.51      | ~ l1_pre_topc(X1) ),
% 7.27/1.51      inference(renaming,[status(thm)],[c_152]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_354,plain,
% 7.27/1.51      ( ~ m1_connsp_2(X0,X1,X2)
% 7.27/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.27/1.51      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.27/1.51      | ~ v2_pre_topc(X1)
% 7.27/1.51      | ~ l1_pre_topc(X1)
% 7.27/1.51      | sK1 != X1 ),
% 7.27/1.51      inference(resolution_lifted,[status(thm)],[c_153,c_26]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_355,plain,
% 7.27/1.51      ( ~ m1_connsp_2(X0,sK1,X1)
% 7.27/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.27/1.51      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 7.27/1.51      | ~ v2_pre_topc(sK1)
% 7.27/1.51      | ~ l1_pre_topc(sK1) ),
% 7.27/1.51      inference(unflattening,[status(thm)],[c_354]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_359,plain,
% 7.27/1.51      ( ~ m1_connsp_2(X0,sK1,X1)
% 7.27/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.27/1.51      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_355,c_25,c_24]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_549,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.27/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.27/1.51      | r2_hidden(X1,k1_tops_1(sK1,X2))
% 7.27/1.51      | ~ r2_hidden(X0,sK2)
% 7.27/1.51      | X1 != X0
% 7.27/1.51      | sK4(X0) != X2
% 7.27/1.51      | sK1 != sK1 ),
% 7.27/1.51      inference(resolution_lifted,[status(thm)],[c_21,c_359]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_550,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.27/1.51      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
% 7.27/1.51      | ~ r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(unflattening,[status(thm)],[c_549]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3742,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1)
% 7.27/1.51      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0)))
% 7.27/1.51      | ~ r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(backward_subsumption_resolution,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_3735,c_550]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_11465,plain,
% 7.27/1.51      ( r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) | ~ r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(backward_subsumption_resolution,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_11426,c_3742]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_22704,plain,
% 7.27/1.51      ( r2_hidden(X0,k1_tops_1(sK1,sK2))
% 7.27/1.51      | ~ r2_hidden(X0,sK2)
% 7.27/1.51      | ~ r1_tarski(sK4(X0),sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_22094,c_11465]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2077,plain,
% 7.27/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 7.27/1.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.27/1.51      | r2_hidden(X0,X2) != iProver_top ),
% 7.27/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3428,plain,
% 7.27/1.51      ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 7.27/1.51      | r2_hidden(X0,sK2) != iProver_top ),
% 7.27/1.51      inference(superposition,[status(thm)],[c_2072,c_2077]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3452,plain,
% 7.27/1.51      ( m1_subset_1(X0,u1_struct_0(sK1)) | ~ r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3428]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_20,negated_conjecture,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.27/1.51      | ~ r2_hidden(X0,sK2)
% 7.27/1.51      | r1_tarski(sK4(X0),sK2) ),
% 7.27/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_3743,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ r2_hidden(X0,sK2)
% 7.27/1.51      | r1_tarski(sK4(X0),sK2) ),
% 7.27/1.51      inference(backward_subsumption_resolution,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_3735,c_20]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_2066,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) = iProver_top
% 7.27/1.51      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 7.27/1.51      | r2_hidden(X0,k1_tops_1(sK1,sK4(X0))) = iProver_top
% 7.27/1.51      | r2_hidden(X0,sK2) != iProver_top ),
% 7.27/1.51      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_9248,plain,
% 7.27/1.51      ( r2_hidden(X0,k1_tops_1(sK1,X1)) != iProver_top
% 7.27/1.51      | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
% 7.27/1.51      | r1_tarski(X1,sK2) != iProver_top ),
% 7.27/1.51      inference(superposition,[status(thm)],[c_8904,c_2083]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_10547,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1) = iProver_top
% 7.27/1.51      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 7.27/1.51      | r2_hidden(X0,k1_tops_1(sK1,sK2)) = iProver_top
% 7.27/1.51      | r2_hidden(X0,sK2) != iProver_top
% 7.27/1.51      | r1_tarski(sK4(X0),sK2) != iProver_top ),
% 7.27/1.51      inference(superposition,[status(thm)],[c_2066,c_9248]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_10567,plain,
% 7.27/1.51      ( v3_pre_topc(sK2,sK1)
% 7.27/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.27/1.51      | r2_hidden(X0,k1_tops_1(sK1,sK2))
% 7.27/1.51      | ~ r2_hidden(X0,sK2)
% 7.27/1.51      | ~ r1_tarski(sK4(X0),sK2) ),
% 7.27/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_10547]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_25025,plain,
% 7.27/1.51      ( ~ r2_hidden(X0,sK2) | r2_hidden(X0,k1_tops_1(sK1,sK2)) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_22704,c_23,c_30,c_41,c_77,c_81,c_2257,c_2259,c_2298,
% 7.27/1.51                 c_3309,c_3377,c_3388,c_3452,c_3743,c_5285,c_10567]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_25026,plain,
% 7.27/1.51      ( r2_hidden(X0,k1_tops_1(sK1,sK2)) | ~ r2_hidden(X0,sK2) ),
% 7.27/1.51      inference(renaming,[status(thm)],[c_25025]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_25043,plain,
% 7.27/1.51      ( ~ r2_hidden(sK0(X0,k1_tops_1(sK1,sK2)),sK2)
% 7.27/1.51      | r1_tarski(X0,k1_tops_1(sK1,sK2)) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_25026,c_0]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_27804,plain,
% 7.27/1.51      ( ~ r1_tarski(sK2,X0) | ~ r1_tarski(X0,sK2) ),
% 7.27/1.51      inference(global_propositional_subsumption,
% 7.27/1.51                [status(thm)],
% 7.27/1.51                [c_27447,c_23,c_30,c_41,c_77,c_81,c_2257,c_2259,c_2695,
% 7.27/1.51                 c_3377,c_3388,c_4427,c_5285,c_18709,c_25043]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_27805,plain,
% 7.27/1.51      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) ),
% 7.27/1.51      inference(renaming,[status(thm)],[c_27804]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(c_27822,plain,
% 7.27/1.51      ( ~ r1_tarski(sK2,sK2) ),
% 7.27/1.51      inference(resolution,[status(thm)],[c_27805,c_5]) ).
% 7.27/1.51  
% 7.27/1.51  cnf(contradiction,plain,
% 7.27/1.51      ( $false ),
% 7.27/1.51      inference(minisat,[status(thm)],[c_27822,c_2298]) ).
% 7.27/1.51  
% 7.27/1.51  
% 7.27/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.27/1.51  
% 7.27/1.51  ------                               Statistics
% 7.27/1.51  
% 7.27/1.51  ------ Selected
% 7.27/1.51  
% 7.27/1.51  total_time:                             0.636
% 7.27/1.51  
%------------------------------------------------------------------------------
