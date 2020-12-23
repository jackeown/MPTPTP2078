%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:52 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 603 expanded)
%              Number of clauses        :   99 ( 129 expanded)
%              Number of leaves         :   17 ( 220 expanded)
%              Depth                    :   29
%              Number of atoms          : 1022 (6186 expanded)
%              Number of equality atoms :  109 ( 616 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( r2_hidden(X1,k10_yellow_6(X0,X2))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                     => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r2_hidden(X1,k10_yellow_6(X0,X2))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                       => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
          & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X1,k2_pre_topc(X0,sK7))
        & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = sK7
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
              & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X1,k10_yellow_6(X0,X2))
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
            & k2_relset_1(u1_struct_0(sK6),u1_struct_0(X0),u1_waybel_0(X0,sK6)) = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(X1,k10_yellow_6(X0,sK6))
        & l1_waybel_0(sK6,X0)
        & v7_waybel_0(sK6)
        & v4_orders_2(sK6)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(sK5,k2_pre_topc(X0,X3))
                & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK5,k10_yellow_6(X0,X2))
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                    & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X1,k10_yellow_6(X0,X2))
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(sK4,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK4),u1_waybel_0(sK4,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
              & r2_hidden(X1,k10_yellow_6(sK4,X2))
              & l1_waybel_0(X2,sK4)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r2_hidden(sK5,k2_pre_topc(sK4,sK7))
    & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))
    & r2_hidden(sK5,k10_yellow_6(sK4,sK6))
    & l1_waybel_0(sK6,sK4)
    & v7_waybel_0(sK6)
    & v4_orders_2(sK6)
    & ~ v2_struct_0(sK6)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f42,f41,f40,f39])).

fof(f71,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK0(X0,X1,X2))
        & r2_hidden(X2,sK0(X0,X1,X2))
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK0(X0,X1,X2))
                    & r2_hidden(X2,sK0(X0,X1,X2))
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    l1_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
        & m1_connsp_2(sK3(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
        & m1_connsp_2(sK2(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK1(X0,X1,X2)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK1(X0,X1,X2)) )
          | r2_hidden(sK1(X0,X1,X2),X2) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
                        & m1_connsp_2(sK2(X0,X1,X2),X0,sK1(X0,X1,X2)) )
                      | ~ r2_hidden(sK1(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK1(X0,X1,X2)) )
                      | r2_hidden(sK1(X0,X1,X2),X2) )
                    & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
                            & m1_connsp_2(sK3(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f52,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X6,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    ~ r2_hidden(sK5,k2_pre_topc(sK4,sK7)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2162,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2552,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_3,plain,
    ( r2_hidden(X0,sK0(X1,X2,X0))
    | r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1509,plain,
    ( r2_hidden(X0,sK0(X1,X2,X0))
    | r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_1510,plain,
    ( r2_hidden(X0,sK0(sK4,X1,X0))
    | r2_hidden(X0,k2_pre_topc(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1509])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1514,plain,
    ( r2_hidden(X0,sK0(sK4,X1,X0))
    | r2_hidden(X0,k2_pre_topc(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1510,c_29,c_28])).

cnf(c_2147,plain,
    ( r2_hidden(X0_56,sK0(sK4,X1_56,X0_56))
    | r2_hidden(X0_56,k2_pre_topc(sK4,X1_56))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1514])).

cnf(c_2567,plain,
    ( r2_hidden(X0_56,sK0(sK4,X1_56,X0_56)) = iProver_top
    | r2_hidden(X0_56,k2_pre_topc(sK4,X1_56)) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2147])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1485,plain,
    ( r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_1486,plain,
    ( r2_hidden(X0,k2_pre_topc(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1485])).

cnf(c_1490,plain,
    ( r2_hidden(X0,k2_pre_topc(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1486,c_29,c_28])).

cnf(c_2148,plain,
    ( r2_hidden(X0_56,k2_pre_topc(sK4,X1_56))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1490])).

cnf(c_2566,plain,
    ( r2_hidden(X0_56,k2_pre_topc(sK4,X1_56)) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK0(sK4,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2148])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1421,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_1422,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_1426,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_29,c_28])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1442,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1426,c_0])).

cnf(c_2149,plain,
    ( m1_connsp_2(X0_56,sK4,X1_56)
    | ~ v3_pre_topc(X0_56,sK4)
    | ~ r2_hidden(X1_56,X0_56)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1442])).

cnf(c_2565,plain,
    ( m1_connsp_2(X0_56,sK4,X1_56) = iProver_top
    | v3_pre_topc(X0_56,sK4) != iProver_top
    | r2_hidden(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2149])).

cnf(c_3350,plain,
    ( m1_connsp_2(sK0(sK4,X0_56,X1_56),sK4,X2_56) = iProver_top
    | v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4) != iProver_top
    | r2_hidden(X2_56,sK0(sK4,X0_56,X1_56)) != iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2566,c_2565])).

cnf(c_4,plain,
    ( v3_pre_topc(sK0(X0,X1,X2),X0)
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1397,plain,
    ( v3_pre_topc(sK0(X0,X1,X2),X0)
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_1398,plain,
    ( v3_pre_topc(sK0(sK4,X0,X1),sK4)
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1397])).

cnf(c_1402,plain,
    ( v3_pre_topc(sK0(sK4,X0,X1),sK4)
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1398,c_29,c_28])).

cnf(c_2150,plain,
    ( v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4)
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1402])).

cnf(c_2209,plain,
    ( v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4) = iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2150])).

cnf(c_3550,plain,
    ( m1_connsp_2(sK0(sK4,X0_56,X1_56),sK4,X2_56) = iProver_top
    | r2_hidden(X2_56,sK0(sK4,X0_56,X1_56)) != iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3350,c_2209])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2161,negated_conjecture,
    ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2553,plain,
    ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_22,negated_conjecture,
    ( l1_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_15,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_833,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_834,plain,
    ( ~ l1_waybel_0(sK6,X0)
    | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_838,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(sK6,X0)
    | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_834,c_25,c_24])).

cnf(c_839,plain,
    ( ~ l1_waybel_0(sK6,X0)
    | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_838])).

cnf(c_14,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_connsp_2(X2,X0,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_609,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_connsp_2(X2,X0,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_610,plain,
    ( r1_waybel_0(X0,sK6,X1)
    | ~ m1_connsp_2(X1,X0,X2)
    | ~ l1_waybel_0(sK6,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_614,plain,
    ( v2_struct_0(X0)
    | r1_waybel_0(X0,sK6,X1)
    | ~ m1_connsp_2(X1,X0,X2)
    | ~ l1_waybel_0(sK6,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_25,c_24])).

cnf(c_615,plain,
    ( r1_waybel_0(X0,sK6,X1)
    | ~ m1_connsp_2(X1,X0,X2)
    | ~ l1_waybel_0(sK6,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_614])).

cnf(c_638,plain,
    ( r1_waybel_0(X0,sK6,X1)
    | ~ m1_connsp_2(X1,X0,X2)
    | ~ l1_waybel_0(sK6,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_615,c_0])).

cnf(c_856,plain,
    ( r1_waybel_0(X0,sK6,X1)
    | ~ m1_connsp_2(X1,X0,X2)
    | ~ l1_waybel_0(sK6,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_839,c_638])).

cnf(c_1141,plain,
    ( r1_waybel_0(X0,sK6,X1)
    | ~ m1_connsp_2(X1,X0,X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != sK6
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_856])).

cnf(c_1142,plain,
    ( r1_waybel_0(sK4,sK6,X0)
    | ~ m1_connsp_2(X0,sK4,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1141])).

cnf(c_1146,plain,
    ( ~ r2_hidden(X1,k10_yellow_6(sK4,sK6))
    | ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1142,c_29,c_28,c_27])).

cnf(c_1147,plain,
    ( r1_waybel_0(sK4,sK6,X0)
    | ~ m1_connsp_2(X0,sK4,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_1146])).

cnf(c_2155,plain,
    ( r1_waybel_0(sK4,sK6,X0_56)
    | ~ m1_connsp_2(X0_56,sK4,X1_56)
    | ~ r2_hidden(X1_56,k10_yellow_6(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_1147])).

cnf(c_2559,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) = iProver_top
    | m1_connsp_2(X0_56,sK4,X1_56) != iProver_top
    | r2_hidden(X1_56,k10_yellow_6(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2155])).

cnf(c_2982,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) = iProver_top
    | m1_connsp_2(X0_56,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_2559])).

cnf(c_3562,plain,
    ( r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56)) = iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | r2_hidden(sK5,sK0(sK4,X0_56,X1_56)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3550,c_2982])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_340,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_16])).

cnf(c_579,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_340,c_23])).

cnf(c_580,plain,
    ( ~ r1_waybel_0(X0,sK6,X1)
    | ~ r1_waybel_0(X0,sK6,X2)
    | ~ l1_waybel_0(sK6,X0)
    | ~ r1_xboole_0(X1,X2)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_584,plain,
    ( v2_struct_0(X0)
    | ~ r1_waybel_0(X0,sK6,X1)
    | ~ r1_waybel_0(X0,sK6,X2)
    | ~ l1_waybel_0(sK6,X0)
    | ~ r1_xboole_0(X1,X2)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_25,c_24])).

cnf(c_585,plain,
    ( ~ r1_waybel_0(X0,sK6,X1)
    | ~ r1_waybel_0(X0,sK6,X2)
    | ~ l1_waybel_0(sK6,X0)
    | ~ r1_xboole_0(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_584])).

cnf(c_1248,plain,
    ( ~ r1_waybel_0(X0,sK6,X1)
    | ~ r1_waybel_0(X0,sK6,X2)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != sK6
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_585])).

cnf(c_1249,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_waybel_0(sK4,sK6,X1)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1248])).

cnf(c_1253,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_waybel_0(sK4,sK6,X1)
    | ~ r1_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1249,c_29,c_27])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,sK0(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1533,plain,
    ( r1_xboole_0(X0,sK0(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_27])).

cnf(c_1534,plain,
    ( r1_xboole_0(X0,sK0(sK4,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1533])).

cnf(c_1538,plain,
    ( r1_xboole_0(X0,sK0(sK4,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1534,c_29,c_28])).

cnf(c_1615,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_waybel_0(sK4,sK6,X1)
    | r2_hidden(X2,k2_pre_topc(sK4,X3))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | X3 != X1
    | sK0(sK4,X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1253,c_1538])).

cnf(c_1616,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_waybel_0(sK4,sK6,sK0(sK4,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_1615])).

cnf(c_2145,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0_56)
    | ~ r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56))
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1616])).

cnf(c_2569,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
    | r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56)) != iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2145])).

cnf(c_3601,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | r2_hidden(sK5,sK0(sK4,X0_56,X1_56)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3562,c_2569])).

cnf(c_3947,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2567,c_3601])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3952,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
    | r1_waybel_0(sK4,sK6,X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3947,c_33])).

cnf(c_3953,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3952])).

cnf(c_3961,plain,
    ( r1_waybel_0(sK4,sK6,sK7) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK4,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_3953])).

cnf(c_17,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_320,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_17])).

cnf(c_1067,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_22])).

cnf(c_1068,plain,
    ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)))
    | v2_struct_0(sK6)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1067])).

cnf(c_1070,plain,
    ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1068,c_29,c_27,c_25])).

cnf(c_2159,plain,
    ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) ),
    inference(subtyping,[status(esa)],[c_1070])).

cnf(c_2555,plain,
    ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2159])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2163,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2582,plain,
    ( r1_waybel_0(sK4,sK6,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2555,c_2163])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK5,k2_pre_topc(sK4,sK7)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( r2_hidden(sK5,k2_pre_topc(sK4,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3961,c_2582,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:52:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.76/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.76/0.99  
% 1.76/0.99  ------  iProver source info
% 1.76/0.99  
% 1.76/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.76/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.76/0.99  git: non_committed_changes: false
% 1.76/0.99  git: last_make_outside_of_git: false
% 1.76/0.99  
% 1.76/0.99  ------ 
% 1.76/0.99  
% 1.76/0.99  ------ Input Options
% 1.76/0.99  
% 1.76/0.99  --out_options                           all
% 1.76/0.99  --tptp_safe_out                         true
% 1.76/0.99  --problem_path                          ""
% 1.76/0.99  --include_path                          ""
% 1.76/0.99  --clausifier                            res/vclausify_rel
% 1.76/0.99  --clausifier_options                    --mode clausify
% 1.76/0.99  --stdin                                 false
% 1.76/0.99  --stats_out                             all
% 1.76/0.99  
% 1.76/0.99  ------ General Options
% 1.76/0.99  
% 1.76/0.99  --fof                                   false
% 1.76/0.99  --time_out_real                         305.
% 1.76/0.99  --time_out_virtual                      -1.
% 1.76/0.99  --symbol_type_check                     false
% 1.76/0.99  --clausify_out                          false
% 1.76/0.99  --sig_cnt_out                           false
% 1.76/0.99  --trig_cnt_out                          false
% 1.76/0.99  --trig_cnt_out_tolerance                1.
% 1.76/0.99  --trig_cnt_out_sk_spl                   false
% 1.76/0.99  --abstr_cl_out                          false
% 1.76/0.99  
% 1.76/0.99  ------ Global Options
% 1.76/0.99  
% 1.76/0.99  --schedule                              default
% 1.76/0.99  --add_important_lit                     false
% 1.76/0.99  --prop_solver_per_cl                    1000
% 1.76/0.99  --min_unsat_core                        false
% 1.76/0.99  --soft_assumptions                      false
% 1.76/0.99  --soft_lemma_size                       3
% 1.76/0.99  --prop_impl_unit_size                   0
% 1.76/0.99  --prop_impl_unit                        []
% 1.76/0.99  --share_sel_clauses                     true
% 1.76/0.99  --reset_solvers                         false
% 1.76/0.99  --bc_imp_inh                            [conj_cone]
% 1.76/0.99  --conj_cone_tolerance                   3.
% 1.76/0.99  --extra_neg_conj                        none
% 1.76/0.99  --large_theory_mode                     true
% 1.76/0.99  --prolific_symb_bound                   200
% 1.76/0.99  --lt_threshold                          2000
% 1.76/0.99  --clause_weak_htbl                      true
% 1.76/0.99  --gc_record_bc_elim                     false
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing Options
% 1.76/0.99  
% 1.76/0.99  --preprocessing_flag                    true
% 1.76/0.99  --time_out_prep_mult                    0.1
% 1.76/0.99  --splitting_mode                        input
% 1.76/0.99  --splitting_grd                         true
% 1.76/0.99  --splitting_cvd                         false
% 1.76/0.99  --splitting_cvd_svl                     false
% 1.76/0.99  --splitting_nvd                         32
% 1.76/0.99  --sub_typing                            true
% 1.76/0.99  --prep_gs_sim                           true
% 1.76/0.99  --prep_unflatten                        true
% 1.76/0.99  --prep_res_sim                          true
% 1.76/0.99  --prep_upred                            true
% 1.76/0.99  --prep_sem_filter                       exhaustive
% 1.76/0.99  --prep_sem_filter_out                   false
% 1.76/0.99  --pred_elim                             true
% 1.76/0.99  --res_sim_input                         true
% 1.76/0.99  --eq_ax_congr_red                       true
% 1.76/0.99  --pure_diseq_elim                       true
% 1.76/0.99  --brand_transform                       false
% 1.76/0.99  --non_eq_to_eq                          false
% 1.76/0.99  --prep_def_merge                        true
% 1.76/0.99  --prep_def_merge_prop_impl              false
% 1.76/0.99  --prep_def_merge_mbd                    true
% 1.76/0.99  --prep_def_merge_tr_red                 false
% 1.76/0.99  --prep_def_merge_tr_cl                  false
% 1.76/0.99  --smt_preprocessing                     true
% 1.76/0.99  --smt_ac_axioms                         fast
% 1.76/0.99  --preprocessed_out                      false
% 1.76/0.99  --preprocessed_stats                    false
% 1.76/0.99  
% 1.76/0.99  ------ Abstraction refinement Options
% 1.76/0.99  
% 1.76/0.99  --abstr_ref                             []
% 1.76/0.99  --abstr_ref_prep                        false
% 1.76/0.99  --abstr_ref_until_sat                   false
% 1.76/0.99  --abstr_ref_sig_restrict                funpre
% 1.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/0.99  --abstr_ref_under                       []
% 1.76/0.99  
% 1.76/0.99  ------ SAT Options
% 1.76/0.99  
% 1.76/0.99  --sat_mode                              false
% 1.76/0.99  --sat_fm_restart_options                ""
% 1.76/0.99  --sat_gr_def                            false
% 1.76/0.99  --sat_epr_types                         true
% 1.76/0.99  --sat_non_cyclic_types                  false
% 1.76/0.99  --sat_finite_models                     false
% 1.76/0.99  --sat_fm_lemmas                         false
% 1.76/0.99  --sat_fm_prep                           false
% 1.76/0.99  --sat_fm_uc_incr                        true
% 1.76/0.99  --sat_out_model                         small
% 1.76/0.99  --sat_out_clauses                       false
% 1.76/0.99  
% 1.76/0.99  ------ QBF Options
% 1.76/0.99  
% 1.76/0.99  --qbf_mode                              false
% 1.76/0.99  --qbf_elim_univ                         false
% 1.76/0.99  --qbf_dom_inst                          none
% 1.76/0.99  --qbf_dom_pre_inst                      false
% 1.76/0.99  --qbf_sk_in                             false
% 1.76/0.99  --qbf_pred_elim                         true
% 1.76/0.99  --qbf_split                             512
% 1.76/0.99  
% 1.76/0.99  ------ BMC1 Options
% 1.76/0.99  
% 1.76/0.99  --bmc1_incremental                      false
% 1.76/0.99  --bmc1_axioms                           reachable_all
% 1.76/0.99  --bmc1_min_bound                        0
% 1.76/0.99  --bmc1_max_bound                        -1
% 1.76/0.99  --bmc1_max_bound_default                -1
% 1.76/0.99  --bmc1_symbol_reachability              true
% 1.76/0.99  --bmc1_property_lemmas                  false
% 1.76/0.99  --bmc1_k_induction                      false
% 1.76/0.99  --bmc1_non_equiv_states                 false
% 1.76/0.99  --bmc1_deadlock                         false
% 1.76/0.99  --bmc1_ucm                              false
% 1.76/0.99  --bmc1_add_unsat_core                   none
% 1.76/0.99  --bmc1_unsat_core_children              false
% 1.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/0.99  --bmc1_out_stat                         full
% 1.76/0.99  --bmc1_ground_init                      false
% 1.76/0.99  --bmc1_pre_inst_next_state              false
% 1.76/0.99  --bmc1_pre_inst_state                   false
% 1.76/0.99  --bmc1_pre_inst_reach_state             false
% 1.76/0.99  --bmc1_out_unsat_core                   false
% 1.76/0.99  --bmc1_aig_witness_out                  false
% 1.76/0.99  --bmc1_verbose                          false
% 1.76/0.99  --bmc1_dump_clauses_tptp                false
% 1.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.76/0.99  --bmc1_dump_file                        -
% 1.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.76/0.99  --bmc1_ucm_extend_mode                  1
% 1.76/0.99  --bmc1_ucm_init_mode                    2
% 1.76/0.99  --bmc1_ucm_cone_mode                    none
% 1.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.76/0.99  --bmc1_ucm_relax_model                  4
% 1.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/0.99  --bmc1_ucm_layered_model                none
% 1.76/0.99  --bmc1_ucm_max_lemma_size               10
% 1.76/0.99  
% 1.76/0.99  ------ AIG Options
% 1.76/0.99  
% 1.76/0.99  --aig_mode                              false
% 1.76/0.99  
% 1.76/0.99  ------ Instantiation Options
% 1.76/0.99  
% 1.76/0.99  --instantiation_flag                    true
% 1.76/0.99  --inst_sos_flag                         false
% 1.76/0.99  --inst_sos_phase                        true
% 1.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/0.99  --inst_lit_sel_side                     num_symb
% 1.76/0.99  --inst_solver_per_active                1400
% 1.76/0.99  --inst_solver_calls_frac                1.
% 1.76/0.99  --inst_passive_queue_type               priority_queues
% 1.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/0.99  --inst_passive_queues_freq              [25;2]
% 1.76/0.99  --inst_dismatching                      true
% 1.76/0.99  --inst_eager_unprocessed_to_passive     true
% 1.76/0.99  --inst_prop_sim_given                   true
% 1.76/0.99  --inst_prop_sim_new                     false
% 1.76/0.99  --inst_subs_new                         false
% 1.76/0.99  --inst_eq_res_simp                      false
% 1.76/0.99  --inst_subs_given                       false
% 1.76/0.99  --inst_orphan_elimination               true
% 1.76/0.99  --inst_learning_loop_flag               true
% 1.76/0.99  --inst_learning_start                   3000
% 1.76/0.99  --inst_learning_factor                  2
% 1.76/0.99  --inst_start_prop_sim_after_learn       3
% 1.76/0.99  --inst_sel_renew                        solver
% 1.76/0.99  --inst_lit_activity_flag                true
% 1.76/0.99  --inst_restr_to_given                   false
% 1.76/0.99  --inst_activity_threshold               500
% 1.76/0.99  --inst_out_proof                        true
% 1.76/0.99  
% 1.76/0.99  ------ Resolution Options
% 1.76/0.99  
% 1.76/0.99  --resolution_flag                       true
% 1.76/0.99  --res_lit_sel                           adaptive
% 1.76/0.99  --res_lit_sel_side                      none
% 1.76/0.99  --res_ordering                          kbo
% 1.76/0.99  --res_to_prop_solver                    active
% 1.76/0.99  --res_prop_simpl_new                    false
% 1.76/0.99  --res_prop_simpl_given                  true
% 1.76/0.99  --res_passive_queue_type                priority_queues
% 1.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/0.99  --res_passive_queues_freq               [15;5]
% 1.76/0.99  --res_forward_subs                      full
% 1.76/0.99  --res_backward_subs                     full
% 1.76/0.99  --res_forward_subs_resolution           true
% 1.76/0.99  --res_backward_subs_resolution          true
% 1.76/0.99  --res_orphan_elimination                true
% 1.76/0.99  --res_time_limit                        2.
% 1.76/0.99  --res_out_proof                         true
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Options
% 1.76/0.99  
% 1.76/0.99  --superposition_flag                    true
% 1.76/0.99  --sup_passive_queue_type                priority_queues
% 1.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.76/0.99  --demod_completeness_check              fast
% 1.76/0.99  --demod_use_ground                      true
% 1.76/0.99  --sup_to_prop_solver                    passive
% 1.76/0.99  --sup_prop_simpl_new                    true
% 1.76/0.99  --sup_prop_simpl_given                  true
% 1.76/0.99  --sup_fun_splitting                     false
% 1.76/0.99  --sup_smt_interval                      50000
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Simplification Setup
% 1.76/0.99  
% 1.76/0.99  --sup_indices_passive                   []
% 1.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_full_bw                           [BwDemod]
% 1.76/0.99  --sup_immed_triv                        [TrivRules]
% 1.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_immed_bw_main                     []
% 1.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  
% 1.76/0.99  ------ Combination Options
% 1.76/0.99  
% 1.76/0.99  --comb_res_mult                         3
% 1.76/0.99  --comb_sup_mult                         2
% 1.76/0.99  --comb_inst_mult                        10
% 1.76/0.99  
% 1.76/0.99  ------ Debug Options
% 1.76/0.99  
% 1.76/0.99  --dbg_backtrace                         false
% 1.76/0.99  --dbg_dump_prop_clauses                 false
% 1.76/0.99  --dbg_dump_prop_clauses_file            -
% 1.76/0.99  --dbg_out_stat                          false
% 1.76/0.99  ------ Parsing...
% 1.76/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.76/0.99  ------ Proving...
% 1.76/0.99  ------ Problem Properties 
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  clauses                                 21
% 1.76/0.99  conjectures                             5
% 1.76/0.99  EPR                                     0
% 1.76/0.99  Horn                                    14
% 1.76/0.99  unary                                   7
% 1.76/0.99  binary                                  0
% 1.76/0.99  lits                                    61
% 1.76/0.99  lits eq                                 5
% 1.76/0.99  fd_pure                                 0
% 1.76/0.99  fd_pseudo                               0
% 1.76/0.99  fd_cond                                 4
% 1.76/0.99  fd_pseudo_cond                          0
% 1.76/0.99  AC symbols                              0
% 1.76/0.99  
% 1.76/0.99  ------ Schedule dynamic 5 is on 
% 1.76/0.99  
% 1.76/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  ------ 
% 1.76/0.99  Current options:
% 1.76/0.99  ------ 
% 1.76/0.99  
% 1.76/0.99  ------ Input Options
% 1.76/0.99  
% 1.76/0.99  --out_options                           all
% 1.76/0.99  --tptp_safe_out                         true
% 1.76/0.99  --problem_path                          ""
% 1.76/0.99  --include_path                          ""
% 1.76/0.99  --clausifier                            res/vclausify_rel
% 1.76/0.99  --clausifier_options                    --mode clausify
% 1.76/0.99  --stdin                                 false
% 1.76/0.99  --stats_out                             all
% 1.76/0.99  
% 1.76/0.99  ------ General Options
% 1.76/0.99  
% 1.76/0.99  --fof                                   false
% 1.76/0.99  --time_out_real                         305.
% 1.76/0.99  --time_out_virtual                      -1.
% 1.76/0.99  --symbol_type_check                     false
% 1.76/0.99  --clausify_out                          false
% 1.76/0.99  --sig_cnt_out                           false
% 1.76/0.99  --trig_cnt_out                          false
% 1.76/0.99  --trig_cnt_out_tolerance                1.
% 1.76/0.99  --trig_cnt_out_sk_spl                   false
% 1.76/0.99  --abstr_cl_out                          false
% 1.76/0.99  
% 1.76/0.99  ------ Global Options
% 1.76/0.99  
% 1.76/0.99  --schedule                              default
% 1.76/0.99  --add_important_lit                     false
% 1.76/0.99  --prop_solver_per_cl                    1000
% 1.76/0.99  --min_unsat_core                        false
% 1.76/0.99  --soft_assumptions                      false
% 1.76/0.99  --soft_lemma_size                       3
% 1.76/0.99  --prop_impl_unit_size                   0
% 1.76/0.99  --prop_impl_unit                        []
% 1.76/0.99  --share_sel_clauses                     true
% 1.76/0.99  --reset_solvers                         false
% 1.76/0.99  --bc_imp_inh                            [conj_cone]
% 1.76/0.99  --conj_cone_tolerance                   3.
% 1.76/0.99  --extra_neg_conj                        none
% 1.76/0.99  --large_theory_mode                     true
% 1.76/0.99  --prolific_symb_bound                   200
% 1.76/0.99  --lt_threshold                          2000
% 1.76/0.99  --clause_weak_htbl                      true
% 1.76/0.99  --gc_record_bc_elim                     false
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing Options
% 1.76/0.99  
% 1.76/0.99  --preprocessing_flag                    true
% 1.76/0.99  --time_out_prep_mult                    0.1
% 1.76/0.99  --splitting_mode                        input
% 1.76/0.99  --splitting_grd                         true
% 1.76/0.99  --splitting_cvd                         false
% 1.76/0.99  --splitting_cvd_svl                     false
% 1.76/0.99  --splitting_nvd                         32
% 1.76/0.99  --sub_typing                            true
% 1.76/0.99  --prep_gs_sim                           true
% 1.76/0.99  --prep_unflatten                        true
% 1.76/0.99  --prep_res_sim                          true
% 1.76/0.99  --prep_upred                            true
% 1.76/0.99  --prep_sem_filter                       exhaustive
% 1.76/0.99  --prep_sem_filter_out                   false
% 1.76/0.99  --pred_elim                             true
% 1.76/0.99  --res_sim_input                         true
% 1.76/0.99  --eq_ax_congr_red                       true
% 1.76/0.99  --pure_diseq_elim                       true
% 1.76/0.99  --brand_transform                       false
% 1.76/0.99  --non_eq_to_eq                          false
% 1.76/0.99  --prep_def_merge                        true
% 1.76/0.99  --prep_def_merge_prop_impl              false
% 1.76/0.99  --prep_def_merge_mbd                    true
% 1.76/0.99  --prep_def_merge_tr_red                 false
% 1.76/0.99  --prep_def_merge_tr_cl                  false
% 1.76/0.99  --smt_preprocessing                     true
% 1.76/0.99  --smt_ac_axioms                         fast
% 1.76/0.99  --preprocessed_out                      false
% 1.76/0.99  --preprocessed_stats                    false
% 1.76/0.99  
% 1.76/0.99  ------ Abstraction refinement Options
% 1.76/0.99  
% 1.76/0.99  --abstr_ref                             []
% 1.76/0.99  --abstr_ref_prep                        false
% 1.76/0.99  --abstr_ref_until_sat                   false
% 1.76/0.99  --abstr_ref_sig_restrict                funpre
% 1.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/0.99  --abstr_ref_under                       []
% 1.76/0.99  
% 1.76/0.99  ------ SAT Options
% 1.76/0.99  
% 1.76/0.99  --sat_mode                              false
% 1.76/0.99  --sat_fm_restart_options                ""
% 1.76/0.99  --sat_gr_def                            false
% 1.76/0.99  --sat_epr_types                         true
% 1.76/0.99  --sat_non_cyclic_types                  false
% 1.76/0.99  --sat_finite_models                     false
% 1.76/0.99  --sat_fm_lemmas                         false
% 1.76/0.99  --sat_fm_prep                           false
% 1.76/0.99  --sat_fm_uc_incr                        true
% 1.76/0.99  --sat_out_model                         small
% 1.76/0.99  --sat_out_clauses                       false
% 1.76/0.99  
% 1.76/0.99  ------ QBF Options
% 1.76/0.99  
% 1.76/0.99  --qbf_mode                              false
% 1.76/0.99  --qbf_elim_univ                         false
% 1.76/0.99  --qbf_dom_inst                          none
% 1.76/0.99  --qbf_dom_pre_inst                      false
% 1.76/0.99  --qbf_sk_in                             false
% 1.76/0.99  --qbf_pred_elim                         true
% 1.76/0.99  --qbf_split                             512
% 1.76/0.99  
% 1.76/0.99  ------ BMC1 Options
% 1.76/0.99  
% 1.76/0.99  --bmc1_incremental                      false
% 1.76/0.99  --bmc1_axioms                           reachable_all
% 1.76/0.99  --bmc1_min_bound                        0
% 1.76/0.99  --bmc1_max_bound                        -1
% 1.76/0.99  --bmc1_max_bound_default                -1
% 1.76/0.99  --bmc1_symbol_reachability              true
% 1.76/0.99  --bmc1_property_lemmas                  false
% 1.76/0.99  --bmc1_k_induction                      false
% 1.76/0.99  --bmc1_non_equiv_states                 false
% 1.76/0.99  --bmc1_deadlock                         false
% 1.76/0.99  --bmc1_ucm                              false
% 1.76/0.99  --bmc1_add_unsat_core                   none
% 1.76/0.99  --bmc1_unsat_core_children              false
% 1.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/0.99  --bmc1_out_stat                         full
% 1.76/0.99  --bmc1_ground_init                      false
% 1.76/0.99  --bmc1_pre_inst_next_state              false
% 1.76/0.99  --bmc1_pre_inst_state                   false
% 1.76/0.99  --bmc1_pre_inst_reach_state             false
% 1.76/0.99  --bmc1_out_unsat_core                   false
% 1.76/0.99  --bmc1_aig_witness_out                  false
% 1.76/0.99  --bmc1_verbose                          false
% 1.76/0.99  --bmc1_dump_clauses_tptp                false
% 1.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.76/0.99  --bmc1_dump_file                        -
% 1.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.76/0.99  --bmc1_ucm_extend_mode                  1
% 1.76/0.99  --bmc1_ucm_init_mode                    2
% 1.76/0.99  --bmc1_ucm_cone_mode                    none
% 1.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.76/0.99  --bmc1_ucm_relax_model                  4
% 1.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/0.99  --bmc1_ucm_layered_model                none
% 1.76/0.99  --bmc1_ucm_max_lemma_size               10
% 1.76/0.99  
% 1.76/0.99  ------ AIG Options
% 1.76/0.99  
% 1.76/0.99  --aig_mode                              false
% 1.76/0.99  
% 1.76/0.99  ------ Instantiation Options
% 1.76/0.99  
% 1.76/0.99  --instantiation_flag                    true
% 1.76/0.99  --inst_sos_flag                         false
% 1.76/0.99  --inst_sos_phase                        true
% 1.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/0.99  --inst_lit_sel_side                     none
% 1.76/0.99  --inst_solver_per_active                1400
% 1.76/0.99  --inst_solver_calls_frac                1.
% 1.76/0.99  --inst_passive_queue_type               priority_queues
% 1.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/0.99  --inst_passive_queues_freq              [25;2]
% 1.76/0.99  --inst_dismatching                      true
% 1.76/0.99  --inst_eager_unprocessed_to_passive     true
% 1.76/0.99  --inst_prop_sim_given                   true
% 1.76/0.99  --inst_prop_sim_new                     false
% 1.76/0.99  --inst_subs_new                         false
% 1.76/0.99  --inst_eq_res_simp                      false
% 1.76/0.99  --inst_subs_given                       false
% 1.76/0.99  --inst_orphan_elimination               true
% 1.76/0.99  --inst_learning_loop_flag               true
% 1.76/0.99  --inst_learning_start                   3000
% 1.76/0.99  --inst_learning_factor                  2
% 1.76/0.99  --inst_start_prop_sim_after_learn       3
% 1.76/0.99  --inst_sel_renew                        solver
% 1.76/0.99  --inst_lit_activity_flag                true
% 1.76/0.99  --inst_restr_to_given                   false
% 1.76/0.99  --inst_activity_threshold               500
% 1.76/0.99  --inst_out_proof                        true
% 1.76/0.99  
% 1.76/0.99  ------ Resolution Options
% 1.76/0.99  
% 1.76/0.99  --resolution_flag                       false
% 1.76/0.99  --res_lit_sel                           adaptive
% 1.76/0.99  --res_lit_sel_side                      none
% 1.76/0.99  --res_ordering                          kbo
% 1.76/0.99  --res_to_prop_solver                    active
% 1.76/0.99  --res_prop_simpl_new                    false
% 1.76/0.99  --res_prop_simpl_given                  true
% 1.76/0.99  --res_passive_queue_type                priority_queues
% 1.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/0.99  --res_passive_queues_freq               [15;5]
% 1.76/0.99  --res_forward_subs                      full
% 1.76/0.99  --res_backward_subs                     full
% 1.76/0.99  --res_forward_subs_resolution           true
% 1.76/0.99  --res_backward_subs_resolution          true
% 1.76/0.99  --res_orphan_elimination                true
% 1.76/0.99  --res_time_limit                        2.
% 1.76/0.99  --res_out_proof                         true
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Options
% 1.76/0.99  
% 1.76/0.99  --superposition_flag                    true
% 1.76/0.99  --sup_passive_queue_type                priority_queues
% 1.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.76/0.99  --demod_completeness_check              fast
% 1.76/0.99  --demod_use_ground                      true
% 1.76/0.99  --sup_to_prop_solver                    passive
% 1.76/0.99  --sup_prop_simpl_new                    true
% 1.76/0.99  --sup_prop_simpl_given                  true
% 1.76/0.99  --sup_fun_splitting                     false
% 1.76/0.99  --sup_smt_interval                      50000
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Simplification Setup
% 1.76/0.99  
% 1.76/0.99  --sup_indices_passive                   []
% 1.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_full_bw                           [BwDemod]
% 1.76/0.99  --sup_immed_triv                        [TrivRules]
% 1.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_immed_bw_main                     []
% 1.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  
% 1.76/0.99  ------ Combination Options
% 1.76/0.99  
% 1.76/0.99  --comb_res_mult                         3
% 1.76/0.99  --comb_sup_mult                         2
% 1.76/0.99  --comb_inst_mult                        10
% 1.76/0.99  
% 1.76/0.99  ------ Debug Options
% 1.76/0.99  
% 1.76/0.99  --dbg_backtrace                         false
% 1.76/0.99  --dbg_dump_prop_clauses                 false
% 1.76/0.99  --dbg_dump_prop_clauses_file            -
% 1.76/0.99  --dbg_out_stat                          false
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  ------ Proving...
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  % SZS status Theorem for theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  fof(f9,conjecture,(
% 1.76/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f10,negated_conjecture,(
% 1.76/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 1.76/0.99    inference(negated_conjecture,[],[f9])).
% 1.76/0.99  
% 1.76/0.99  fof(f26,plain,(
% 1.76/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f10])).
% 1.76/0.99  
% 1.76/0.99  fof(f27,plain,(
% 1.76/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f26])).
% 1.76/0.99  
% 1.76/0.99  fof(f42,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X1,k2_pre_topc(X0,sK7)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = sK7 & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f41,plain,(
% 1.76/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(X0),u1_waybel_0(X0,sK6)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,sK6)) & l1_waybel_0(sK6,X0) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f40,plain,(
% 1.76/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~r2_hidden(sK5,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK5,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f39,plain,(
% 1.76/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(sK4,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK4),u1_waybel_0(sK4,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X1,k10_yellow_6(sK4,X2)) & l1_waybel_0(X2,sK4) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f43,plain,(
% 1.76/0.99    (((~r2_hidden(sK5,k2_pre_topc(sK4,sK7)) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK5,k10_yellow_6(sK4,sK6)) & l1_waybel_0(sK6,sK4) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 1.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f42,f41,f40,f39])).
% 1.76/0.99  
% 1.76/0.99  fof(f71,plain,(
% 1.76/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f3,axiom,(
% 1.76/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0)))))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f14,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f3])).
% 1.76/0.99  
% 1.76/0.99  fof(f15,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f14])).
% 1.76/0.99  
% 1.76/0.99  fof(f28,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(nnf_transformation,[],[f15])).
% 1.76/0.99  
% 1.76/0.99  fof(f29,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(rectify,[],[f28])).
% 1.76/0.99  
% 1.76/0.99  fof(f30,plain,(
% 1.76/0.99    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK0(X0,X1,X2)) & r2_hidden(X2,sK0(X0,X1,X2)) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f31,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK0(X0,X1,X2)) & r2_hidden(X2,sK0(X0,X1,X2)) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.76/0.99  
% 1.76/0.99  fof(f49,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r2_hidden(X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f64,plain,(
% 1.76/0.99    l1_pre_topc(sK4)),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f62,plain,(
% 1.76/0.99    ~v2_struct_0(sK4)),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f63,plain,(
% 1.76/0.99    v2_pre_topc(sK4)),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f47,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f4,axiom,(
% 1.76/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f16,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f4])).
% 1.76/0.99  
% 1.76/0.99  fof(f17,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f16])).
% 1.76/0.99  
% 1.76/0.99  fof(f51,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f17])).
% 1.76/0.99  
% 1.76/0.99  fof(f1,axiom,(
% 1.76/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f11,plain,(
% 1.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.76/0.99    inference(ennf_transformation,[],[f1])).
% 1.76/0.99  
% 1.76/0.99  fof(f12,plain,(
% 1.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.76/0.99    inference(flattening,[],[f11])).
% 1.76/0.99  
% 1.76/0.99  fof(f44,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f12])).
% 1.76/0.99  
% 1.76/0.99  fof(f48,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | v3_pre_topc(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f70,plain,(
% 1.76/0.99    r2_hidden(sK5,k10_yellow_6(sK4,sK6))),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f69,plain,(
% 1.76/0.99    l1_waybel_0(sK6,sK4)),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f6,axiom,(
% 1.76/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f20,plain,(
% 1.76/0.99    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f6])).
% 1.76/0.99  
% 1.76/0.99  fof(f21,plain,(
% 1.76/0.99    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f20])).
% 1.76/0.99  
% 1.76/0.99  fof(f59,plain,(
% 1.76/0.99    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f21])).
% 1.76/0.99  
% 1.76/0.99  fof(f68,plain,(
% 1.76/0.99    v7_waybel_0(sK6)),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f66,plain,(
% 1.76/0.99    ~v2_struct_0(sK6)),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f67,plain,(
% 1.76/0.99    v4_orders_2(sK6)),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f5,axiom,(
% 1.76/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f18,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f5])).
% 1.76/0.99  
% 1.76/0.99  fof(f19,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f18])).
% 1.76/0.99  
% 1.76/0.99  fof(f32,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(nnf_transformation,[],[f19])).
% 1.76/0.99  
% 1.76/0.99  fof(f33,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f32])).
% 1.76/0.99  
% 1.76/0.99  fof(f34,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(rectify,[],[f33])).
% 1.76/0.99  
% 1.76/0.99  fof(f37,plain,(
% 1.76/0.99    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6)))),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f36,plain,(
% 1.76/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,X3)))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f35,plain,(
% 1.76/0.99    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f38,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f52,plain,(
% 1.76/0.99    ( ! [X6,X2,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f38])).
% 1.76/0.99  
% 1.76/0.99  fof(f76,plain,(
% 1.76/0.99    ( ! [X6,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(equality_resolution,[],[f52])).
% 1.76/0.99  
% 1.76/0.99  fof(f2,axiom,(
% 1.76/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f13,plain,(
% 1.76/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.76/0.99    inference(ennf_transformation,[],[f2])).
% 1.76/0.99  
% 1.76/0.99  fof(f45,plain,(
% 1.76/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f13])).
% 1.76/0.99  
% 1.76/0.99  fof(f7,axiom,(
% 1.76/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f22,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f7])).
% 1.76/0.99  
% 1.76/0.99  fof(f23,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f22])).
% 1.76/0.99  
% 1.76/0.99  fof(f60,plain,(
% 1.76/0.99    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f23])).
% 1.76/0.99  
% 1.76/0.99  fof(f50,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_xboole_0(X1,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f65,plain,(
% 1.76/0.99    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f8,axiom,(
% 1.76/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f24,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f8])).
% 1.76/0.99  
% 1.76/0.99  fof(f25,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f24])).
% 1.76/0.99  
% 1.76/0.99  fof(f61,plain,(
% 1.76/0.99    ( ! [X0,X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f25])).
% 1.76/0.99  
% 1.76/0.99  fof(f72,plain,(
% 1.76/0.99    k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  fof(f73,plain,(
% 1.76/0.99    ~r2_hidden(sK5,k2_pre_topc(sK4,sK7))),
% 1.76/0.99    inference(cnf_transformation,[],[f43])).
% 1.76/0.99  
% 1.76/0.99  cnf(c_20,negated_conjecture,
% 1.76/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2162,negated_conjecture,
% 1.76/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2552,plain,
% 1.76/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_3,plain,
% 1.76/0.99      ( r2_hidden(X0,sK0(X1,X2,X0))
% 1.76/0.99      | r2_hidden(X0,k2_pre_topc(X1,X2))
% 1.76/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.76/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X1)
% 1.76/0.99      | ~ l1_pre_topc(X1) ),
% 1.76/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_27,negated_conjecture,
% 1.76/0.99      ( l1_pre_topc(sK4) ),
% 1.76/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1509,plain,
% 1.76/0.99      ( r2_hidden(X0,sK0(X1,X2,X0))
% 1.76/0.99      | r2_hidden(X0,k2_pre_topc(X1,X2))
% 1.76/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.76/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X1)
% 1.76/0.99      | sK4 != X1 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1510,plain,
% 1.76/0.99      ( r2_hidden(X0,sK0(sK4,X1,X0))
% 1.76/0.99      | r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.76/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/0.99      | v2_struct_0(sK4)
% 1.76/0.99      | ~ v2_pre_topc(sK4) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_1509]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_29,negated_conjecture,
% 1.76/0.99      ( ~ v2_struct_0(sK4) ),
% 1.76/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_28,negated_conjecture,
% 1.76/0.99      ( v2_pre_topc(sK4) ),
% 1.76/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1514,plain,
% 1.76/0.99      ( r2_hidden(X0,sK0(sK4,X1,X0))
% 1.76/0.99      | r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.76/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1510,c_29,c_28]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2147,plain,
% 1.76/0.99      ( r2_hidden(X0_56,sK0(sK4,X1_56,X0_56))
% 1.76/0.99      | r2_hidden(X0_56,k2_pre_topc(sK4,X1_56))
% 1.76/0.99      | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_1514]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2567,plain,
% 1.76/0.99      ( r2_hidden(X0_56,sK0(sK4,X1_56,X0_56)) = iProver_top
% 1.76/0.99      | r2_hidden(X0_56,k2_pre_topc(sK4,X1_56)) = iProver_top
% 1.76/0.99      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 1.76/0.99      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2147]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_5,plain,
% 1.76/0.99      ( r2_hidden(X0,k2_pre_topc(X1,X2))
% 1.76/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.76/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X1)
% 1.76/0.99      | ~ l1_pre_topc(X1) ),
% 1.76/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1485,plain,
% 1.76/0.99      ( r2_hidden(X0,k2_pre_topc(X1,X2))
% 1.76/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.76/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X1)
% 1.76/0.99      | sK4 != X1 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1486,plain,
% 1.76/0.99      ( r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.76/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/0.99      | m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/0.99      | v2_struct_0(sK4)
% 1.76/0.99      | ~ v2_pre_topc(sK4) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_1485]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1490,plain,
% 1.76/0.99      ( r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.76/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/0.99      | m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1486,c_29,c_28]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2148,plain,
% 1.76/0.99      ( r2_hidden(X0_56,k2_pre_topc(sK4,X1_56))
% 1.76/0.99      | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/0.99      | m1_subset_1(sK0(sK4,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_1490]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2566,plain,
% 1.76/0.99      ( r2_hidden(X0_56,k2_pre_topc(sK4,X1_56)) = iProver_top
% 1.76/0.99      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 1.76/0.99      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.76/0.99      | m1_subset_1(sK0(sK4,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2148]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_7,plain,
% 1.76/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.76/0.99      | ~ v3_pre_topc(X0,X1)
% 1.76/0.99      | ~ r2_hidden(X2,X0)
% 1.76/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X1)
% 1.76/0.99      | ~ l1_pre_topc(X1) ),
% 1.76/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1421,plain,
% 1.76/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.76/0.99      | ~ v3_pre_topc(X0,X1)
% 1.76/0.99      | ~ r2_hidden(X2,X0)
% 1.76/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X1)
% 1.76/0.99      | sK4 != X1 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1422,plain,
% 1.76/0.99      ( m1_connsp_2(X0,sK4,X1)
% 1.76/0.99      | ~ v3_pre_topc(X0,sK4)
% 1.76/0.99      | ~ r2_hidden(X1,X0)
% 1.76/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/0.99      | v2_struct_0(sK4)
% 1.76/0.99      | ~ v2_pre_topc(sK4) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_1421]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1426,plain,
% 1.76/0.99      ( m1_connsp_2(X0,sK4,X1)
% 1.76/0.99      | ~ v3_pre_topc(X0,sK4)
% 1.76/0.99      | ~ r2_hidden(X1,X0)
% 1.76/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1422,c_29,c_28]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_0,plain,
% 1.76/0.99      ( ~ r2_hidden(X0,X1)
% 1.76/0.99      | m1_subset_1(X0,X2)
% 1.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1442,plain,
% 1.76/0.99      ( m1_connsp_2(X0,sK4,X1)
% 1.76/0.99      | ~ v3_pre_topc(X0,sK4)
% 1.76/0.99      | ~ r2_hidden(X1,X0)
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(forward_subsumption_resolution,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1426,c_0]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2149,plain,
% 1.76/0.99      ( m1_connsp_2(X0_56,sK4,X1_56)
% 1.76/0.99      | ~ v3_pre_topc(X0_56,sK4)
% 1.76/0.99      | ~ r2_hidden(X1_56,X0_56)
% 1.76/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_1442]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2565,plain,
% 1.76/0.99      ( m1_connsp_2(X0_56,sK4,X1_56) = iProver_top
% 1.76/0.99      | v3_pre_topc(X0_56,sK4) != iProver_top
% 1.76/0.99      | r2_hidden(X1_56,X0_56) != iProver_top
% 1.76/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2149]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_3350,plain,
% 1.76/0.99      ( m1_connsp_2(sK0(sK4,X0_56,X1_56),sK4,X2_56) = iProver_top
% 1.76/0.99      | v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4) != iProver_top
% 1.76/0.99      | r2_hidden(X2_56,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.76/0.99      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/0.99      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.76/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_2566,c_2565]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_4,plain,
% 1.76/0.99      ( v3_pre_topc(sK0(X0,X1,X2),X0)
% 1.76/0.99      | r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.76/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1397,plain,
% 1.76/0.99      ( v3_pre_topc(sK0(X0,X1,X2),X0)
% 1.76/0.99      | r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.76/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | sK4 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1398,plain,
% 1.76/0.99      ( v3_pre_topc(sK0(sK4,X0,X1),sK4)
% 1.76/0.99      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.76/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/0.99      | v2_struct_0(sK4)
% 1.76/0.99      | ~ v2_pre_topc(sK4) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_1397]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1402,plain,
% 1.76/0.99      ( v3_pre_topc(sK0(sK4,X0,X1),sK4)
% 1.76/0.99      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.76/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1398,c_29,c_28]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2150,plain,
% 1.76/0.99      ( v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4)
% 1.76/0.99      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56))
% 1.76/0.99      | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
% 1.76/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_1402]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2209,plain,
% 1.76/0.99      ( v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4) = iProver_top
% 1.76/0.99      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/0.99      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.76/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2150]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_3550,plain,
% 1.76/0.99      ( m1_connsp_2(sK0(sK4,X0_56,X1_56),sK4,X2_56) = iProver_top
% 1.76/0.99      | r2_hidden(X2_56,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.76/0.99      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/0.99      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.76/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_3350,c_2209]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_21,negated_conjecture,
% 1.76/0.99      ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2161,negated_conjecture,
% 1.76/0.99      ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2553,plain,
% 1.76/0.99      ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_22,negated_conjecture,
% 1.76/0.99      ( l1_waybel_0(sK6,sK4) ),
% 1.76/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_15,plain,
% 1.76/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.76/0.99      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | ~ v4_orders_2(X0)
% 1.76/0.99      | ~ v7_waybel_0(X0)
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ v2_pre_topc(X1)
% 1.76/0.99      | ~ l1_pre_topc(X1) ),
% 1.76/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_23,negated_conjecture,
% 1.76/0.99      ( v7_waybel_0(sK6) ),
% 1.76/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_833,plain,
% 1.76/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.76/0.99      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/0.99      | ~ v4_orders_2(X0)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X1)
% 1.76/0.99      | ~ l1_pre_topc(X1)
% 1.76/0.99      | sK6 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_834,plain,
% 1.76/0.99      ( ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | ~ v4_orders_2(sK6)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(sK6)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_833]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_25,negated_conjecture,
% 1.76/0.99      ( ~ v2_struct_0(sK6) ),
% 1.76/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_24,negated_conjecture,
% 1.76/0.99      ( v4_orders_2(sK6) ),
% 1.76/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_838,plain,
% 1.76/0.99      ( v2_struct_0(X0)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_834,c_25,c_24]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_839,plain,
% 1.76/0.99      ( ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_838]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_14,plain,
% 1.76/0.99      ( r1_waybel_0(X0,X1,X2)
% 1.76/0.99      | ~ m1_connsp_2(X2,X0,X3)
% 1.76/0.99      | ~ l1_waybel_0(X1,X0)
% 1.76/0.99      | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
% 1.76/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.76/0.99      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | ~ v4_orders_2(X1)
% 1.76/0.99      | ~ v7_waybel_0(X1)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_609,plain,
% 1.76/0.99      ( r1_waybel_0(X0,X1,X2)
% 1.76/0.99      | ~ m1_connsp_2(X2,X0,X3)
% 1.76/0.99      | ~ l1_waybel_0(X1,X0)
% 1.76/0.99      | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
% 1.76/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.76/0.99      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | ~ v4_orders_2(X1)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0)
% 1.76/0.99      | sK6 != X1 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_610,plain,
% 1.76/0.99      ( r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ m1_connsp_2(X1,X0,X2)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
% 1.76/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.76/0.99      | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | ~ v4_orders_2(sK6)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(sK6)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_609]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_614,plain,
% 1.76/0.99      ( v2_struct_0(X0)
% 1.76/0.99      | r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ m1_connsp_2(X1,X0,X2)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
% 1.76/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.76/0.99      | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_610,c_25,c_24]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_615,plain,
% 1.76/0.99      ( r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ m1_connsp_2(X1,X0,X2)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
% 1.76/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.76/0.99      | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_614]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_638,plain,
% 1.76/0.99      ( r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ m1_connsp_2(X1,X0,X2)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
% 1.76/0.99      | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_615,c_0]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_856,plain,
% 1.76/0.99      ( r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ m1_connsp_2(X1,X0,X2)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(backward_subsumption_resolution,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_839,c_638]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1141,plain,
% 1.76/0.99      ( r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ m1_connsp_2(X1,X0,X2)
% 1.76/0.99      | ~ r2_hidden(X2,k10_yellow_6(X0,sK6))
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ v2_pre_topc(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0)
% 1.76/0.99      | sK6 != sK6
% 1.76/0.99      | sK4 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_856]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1142,plain,
% 1.76/0.99      ( r1_waybel_0(sK4,sK6,X0)
% 1.76/0.99      | ~ m1_connsp_2(X0,sK4,X1)
% 1.76/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6))
% 1.76/0.99      | v2_struct_0(sK4)
% 1.76/0.99      | ~ v2_pre_topc(sK4)
% 1.76/0.99      | ~ l1_pre_topc(sK4) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_1141]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1146,plain,
% 1.76/0.99      ( ~ r2_hidden(X1,k10_yellow_6(sK4,sK6))
% 1.76/0.99      | ~ m1_connsp_2(X0,sK4,X1)
% 1.76/0.99      | r1_waybel_0(sK4,sK6,X0) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1142,c_29,c_28,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1147,plain,
% 1.76/0.99      ( r1_waybel_0(sK4,sK6,X0)
% 1.76/0.99      | ~ m1_connsp_2(X0,sK4,X1)
% 1.76/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6)) ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_1146]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2155,plain,
% 1.76/0.99      ( r1_waybel_0(sK4,sK6,X0_56)
% 1.76/0.99      | ~ m1_connsp_2(X0_56,sK4,X1_56)
% 1.76/0.99      | ~ r2_hidden(X1_56,k10_yellow_6(sK4,sK6)) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_1147]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2559,plain,
% 1.76/0.99      ( r1_waybel_0(sK4,sK6,X0_56) = iProver_top
% 1.76/0.99      | m1_connsp_2(X0_56,sK4,X1_56) != iProver_top
% 1.76/0.99      | r2_hidden(X1_56,k10_yellow_6(sK4,sK6)) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2155]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2982,plain,
% 1.76/0.99      ( r1_waybel_0(sK4,sK6,X0_56) = iProver_top
% 1.76/0.99      | m1_connsp_2(X0_56,sK4,sK5) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_2553,c_2559]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_3562,plain,
% 1.76/0.99      ( r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56)) = iProver_top
% 1.76/0.99      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/0.99      | r2_hidden(sK5,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.76/0.99      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.76/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_3550,c_2982]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1,plain,
% 1.76/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_16,plain,
% 1.76/0.99      ( ~ r1_waybel_0(X0,X1,X2)
% 1.76/0.99      | ~ r1_waybel_0(X0,X1,X3)
% 1.76/0.99      | ~ l1_waybel_0(X1,X0)
% 1.76/0.99      | ~ r1_xboole_0(X3,X2)
% 1.76/0.99      | ~ v4_orders_2(X1)
% 1.76/0.99      | ~ v7_waybel_0(X1)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ l1_struct_0(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_340,plain,
% 1.76/0.99      ( ~ r1_waybel_0(X0,X1,X2)
% 1.76/0.99      | ~ r1_waybel_0(X0,X1,X3)
% 1.76/0.99      | ~ l1_waybel_0(X1,X0)
% 1.76/0.99      | ~ r1_xboole_0(X3,X2)
% 1.76/0.99      | ~ v4_orders_2(X1)
% 1.76/0.99      | ~ v7_waybel_0(X1)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(resolution,[status(thm)],[c_1,c_16]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_579,plain,
% 1.76/0.99      ( ~ r1_waybel_0(X0,X1,X2)
% 1.76/0.99      | ~ r1_waybel_0(X0,X1,X3)
% 1.76/0.99      | ~ l1_waybel_0(X1,X0)
% 1.76/0.99      | ~ r1_xboole_0(X3,X2)
% 1.76/0.99      | ~ v4_orders_2(X1)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(X1)
% 1.76/0.99      | ~ l1_pre_topc(X0)
% 1.76/0.99      | sK6 != X1 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_340,c_23]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_580,plain,
% 1.76/0.99      ( ~ r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ r1_waybel_0(X0,sK6,X2)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | ~ r1_xboole_0(X1,X2)
% 1.76/0.99      | ~ v4_orders_2(sK6)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | v2_struct_0(sK6)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_579]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_584,plain,
% 1.76/0.99      ( v2_struct_0(X0)
% 1.76/0.99      | ~ r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ r1_waybel_0(X0,sK6,X2)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | ~ r1_xboole_0(X1,X2)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_580,c_25,c_24]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_585,plain,
% 1.76/0.99      ( ~ r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ r1_waybel_0(X0,sK6,X2)
% 1.76/0.99      | ~ l1_waybel_0(sK6,X0)
% 1.76/0.99      | ~ r1_xboole_0(X2,X1)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0) ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_584]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1248,plain,
% 1.76/0.99      ( ~ r1_waybel_0(X0,sK6,X1)
% 1.76/0.99      | ~ r1_waybel_0(X0,sK6,X2)
% 1.76/0.99      | ~ r1_xboole_0(X1,X2)
% 1.76/0.99      | v2_struct_0(X0)
% 1.76/0.99      | ~ l1_pre_topc(X0)
% 1.76/0.99      | sK6 != sK6
% 1.76/0.99      | sK4 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_585]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1249,plain,
% 1.76/0.99      ( ~ r1_waybel_0(sK4,sK6,X0)
% 1.76/0.99      | ~ r1_waybel_0(sK4,sK6,X1)
% 1.76/0.99      | ~ r1_xboole_0(X1,X0)
% 1.76/0.99      | v2_struct_0(sK4)
% 1.76/1.00      | ~ l1_pre_topc(sK4) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_1248]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1253,plain,
% 1.76/1.00      ( ~ r1_waybel_0(sK4,sK6,X0)
% 1.76/1.00      | ~ r1_waybel_0(sK4,sK6,X1)
% 1.76/1.00      | ~ r1_xboole_0(X1,X0) ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_1249,c_29,c_27]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2,plain,
% 1.76/1.00      ( r1_xboole_0(X0,sK0(X1,X0,X2))
% 1.76/1.00      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/1.00      | v2_struct_0(X1)
% 1.76/1.00      | ~ v2_pre_topc(X1)
% 1.76/1.00      | ~ l1_pre_topc(X1) ),
% 1.76/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1533,plain,
% 1.76/1.00      ( r1_xboole_0(X0,sK0(X1,X0,X2))
% 1.76/1.00      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.76/1.00      | v2_struct_0(X1)
% 1.76/1.00      | ~ v2_pre_topc(X1)
% 1.76/1.00      | sK4 != X1 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_27]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1534,plain,
% 1.76/1.00      ( r1_xboole_0(X0,sK0(sK4,X0,X1))
% 1.76/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/1.00      | v2_struct_0(sK4)
% 1.76/1.00      | ~ v2_pre_topc(sK4) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_1533]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1538,plain,
% 1.76/1.00      ( r1_xboole_0(X0,sK0(sK4,X0,X1))
% 1.76/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_1534,c_29,c_28]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1615,plain,
% 1.76/1.00      ( ~ r1_waybel_0(sK4,sK6,X0)
% 1.76/1.00      | ~ r1_waybel_0(sK4,sK6,X1)
% 1.76/1.00      | r2_hidden(X2,k2_pre_topc(sK4,X3))
% 1.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.76/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.76/1.00      | X3 != X1
% 1.76/1.00      | sK0(sK4,X3,X2) != X0 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_1253,c_1538]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1616,plain,
% 1.76/1.00      ( ~ r1_waybel_0(sK4,sK6,X0)
% 1.76/1.00      | ~ r1_waybel_0(sK4,sK6,sK0(sK4,X0,X1))
% 1.76/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_1615]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2145,plain,
% 1.76/1.00      ( ~ r1_waybel_0(sK4,sK6,X0_56)
% 1.76/1.00      | ~ r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56))
% 1.76/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56))
% 1.76/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
% 1.76/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.76/1.00      inference(subtyping,[status(esa)],[c_1616]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2569,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
% 1.76/1.00      | r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.76/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/1.00      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.76/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2145]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_3601,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
% 1.76/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/1.00      | r2_hidden(sK5,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.76/1.00      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.76/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/1.00      inference(superposition,[status(thm)],[c_3562,c_2569]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_3947,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
% 1.76/1.00      | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.76/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 1.76/1.00      inference(superposition,[status(thm)],[c_2567,c_3601]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_26,negated_conjecture,
% 1.76/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.76/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_33,plain,
% 1.76/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_3952,plain,
% 1.76/1.00      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.76/1.00      | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/1.00      | r1_waybel_0(sK4,sK6,X0_56) != iProver_top ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_3947,c_33]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_3953,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
% 1.76/1.00      | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.76/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.76/1.00      inference(renaming,[status(thm)],[c_3952]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_3961,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,sK7) != iProver_top
% 1.76/1.00      | r2_hidden(sK5,k2_pre_topc(sK4,sK7)) = iProver_top ),
% 1.76/1.00      inference(superposition,[status(thm)],[c_2552,c_3953]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_17,plain,
% 1.76/1.00      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
% 1.76/1.00      | ~ l1_waybel_0(X1,X0)
% 1.76/1.00      | v2_struct_0(X0)
% 1.76/1.00      | v2_struct_0(X1)
% 1.76/1.00      | ~ l1_struct_0(X0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_320,plain,
% 1.76/1.00      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
% 1.76/1.00      | ~ l1_waybel_0(X1,X0)
% 1.76/1.00      | v2_struct_0(X0)
% 1.76/1.00      | v2_struct_0(X1)
% 1.76/1.00      | ~ l1_pre_topc(X0) ),
% 1.76/1.00      inference(resolution,[status(thm)],[c_1,c_17]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1067,plain,
% 1.76/1.00      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
% 1.76/1.00      | v2_struct_0(X0)
% 1.76/1.00      | v2_struct_0(X1)
% 1.76/1.00      | ~ l1_pre_topc(X0)
% 1.76/1.00      | sK6 != X1
% 1.76/1.00      | sK4 != X0 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_320,c_22]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1068,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)))
% 1.76/1.00      | v2_struct_0(sK6)
% 1.76/1.00      | v2_struct_0(sK4)
% 1.76/1.00      | ~ l1_pre_topc(sK4) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_1067]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1070,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_1068,c_29,c_27,c_25]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2159,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) ),
% 1.76/1.00      inference(subtyping,[status(esa)],[c_1070]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2555,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2159]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_19,negated_conjecture,
% 1.76/1.00      ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
% 1.76/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2163,negated_conjecture,
% 1.76/1.00      ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
% 1.76/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2582,plain,
% 1.76/1.00      ( r1_waybel_0(sK4,sK6,sK7) = iProver_top ),
% 1.76/1.00      inference(light_normalisation,[status(thm)],[c_2555,c_2163]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_18,negated_conjecture,
% 1.76/1.00      ( ~ r2_hidden(sK5,k2_pre_topc(sK4,sK7)) ),
% 1.76/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_40,plain,
% 1.76/1.00      ( r2_hidden(sK5,k2_pre_topc(sK4,sK7)) != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(contradiction,plain,
% 1.76/1.00      ( $false ),
% 1.76/1.00      inference(minisat,[status(thm)],[c_3961,c_2582,c_40]) ).
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  ------                               Statistics
% 1.76/1.00  
% 1.76/1.00  ------ General
% 1.76/1.00  
% 1.76/1.00  abstr_ref_over_cycles:                  0
% 1.76/1.00  abstr_ref_under_cycles:                 0
% 1.76/1.00  gc_basic_clause_elim:                   0
% 1.76/1.00  forced_gc_time:                         0
% 1.76/1.00  parsing_time:                           0.012
% 1.76/1.00  unif_index_cands_time:                  0.
% 1.76/1.00  unif_index_add_time:                    0.
% 1.76/1.00  orderings_time:                         0.
% 1.76/1.00  out_proof_time:                         0.012
% 1.76/1.00  total_time:                             0.152
% 1.76/1.00  num_of_symbols:                         59
% 1.76/1.00  num_of_terms:                           3408
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing
% 1.76/1.00  
% 1.76/1.00  num_of_splits:                          0
% 1.76/1.00  num_of_split_atoms:                     0
% 1.76/1.00  num_of_reused_defs:                     0
% 1.76/1.00  num_eq_ax_congr_red:                    50
% 1.76/1.00  num_of_sem_filtered_clauses:            1
% 1.76/1.00  num_of_subtypes:                        4
% 1.76/1.00  monotx_restored_types:                  1
% 1.76/1.00  sat_num_of_epr_types:                   0
% 1.76/1.00  sat_num_of_non_cyclic_types:            0
% 1.76/1.00  sat_guarded_non_collapsed_types:        0
% 1.76/1.00  num_pure_diseq_elim:                    0
% 1.76/1.00  simp_replaced_by:                       0
% 1.76/1.00  res_preprocessed:                       110
% 1.76/1.00  prep_upred:                             0
% 1.76/1.00  prep_unflattend:                        66
% 1.76/1.00  smt_new_axioms:                         0
% 1.76/1.00  pred_elim_cands:                        5
% 1.76/1.00  pred_elim:                              8
% 1.76/1.00  pred_elim_cl:                           9
% 1.76/1.00  pred_elim_cycles:                       16
% 1.76/1.00  merged_defs:                            0
% 1.76/1.00  merged_defs_ncl:                        0
% 1.76/1.00  bin_hyper_res:                          0
% 1.76/1.00  prep_cycles:                            4
% 1.76/1.00  pred_elim_time:                         0.04
% 1.76/1.00  splitting_time:                         0.
% 1.76/1.00  sem_filter_time:                        0.
% 1.76/1.00  monotx_time:                            0.001
% 1.76/1.00  subtype_inf_time:                       0.001
% 1.76/1.00  
% 1.76/1.00  ------ Problem properties
% 1.76/1.00  
% 1.76/1.00  clauses:                                21
% 1.76/1.00  conjectures:                            5
% 1.76/1.00  epr:                                    0
% 1.76/1.00  horn:                                   14
% 1.76/1.00  ground:                                 7
% 1.76/1.00  unary:                                  7
% 1.76/1.00  binary:                                 0
% 1.76/1.00  lits:                                   61
% 1.76/1.00  lits_eq:                                5
% 1.76/1.00  fd_pure:                                0
% 1.76/1.00  fd_pseudo:                              0
% 1.76/1.00  fd_cond:                                4
% 1.76/1.00  fd_pseudo_cond:                         0
% 1.76/1.00  ac_symbols:                             0
% 1.76/1.00  
% 1.76/1.00  ------ Propositional Solver
% 1.76/1.00  
% 1.76/1.00  prop_solver_calls:                      27
% 1.76/1.00  prop_fast_solver_calls:                 1532
% 1.76/1.00  smt_solver_calls:                       0
% 1.76/1.00  smt_fast_solver_calls:                  0
% 1.76/1.00  prop_num_of_clauses:                    992
% 1.76/1.00  prop_preprocess_simplified:             3794
% 1.76/1.00  prop_fo_subsumed:                       77
% 1.76/1.00  prop_solver_time:                       0.
% 1.76/1.00  smt_solver_time:                        0.
% 1.76/1.00  smt_fast_solver_time:                   0.
% 1.76/1.00  prop_fast_solver_time:                  0.
% 1.76/1.00  prop_unsat_core_time:                   0.
% 1.76/1.00  
% 1.76/1.00  ------ QBF
% 1.76/1.00  
% 1.76/1.00  qbf_q_res:                              0
% 1.76/1.00  qbf_num_tautologies:                    0
% 1.76/1.00  qbf_prep_cycles:                        0
% 1.76/1.00  
% 1.76/1.00  ------ BMC1
% 1.76/1.00  
% 1.76/1.00  bmc1_current_bound:                     -1
% 1.76/1.00  bmc1_last_solved_bound:                 -1
% 1.76/1.00  bmc1_unsat_core_size:                   -1
% 1.76/1.00  bmc1_unsat_core_parents_size:           -1
% 1.76/1.00  bmc1_merge_next_fun:                    0
% 1.76/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.76/1.00  
% 1.76/1.00  ------ Instantiation
% 1.76/1.00  
% 1.76/1.00  inst_num_of_clauses:                    187
% 1.76/1.00  inst_num_in_passive:                    11
% 1.76/1.00  inst_num_in_active:                     158
% 1.76/1.00  inst_num_in_unprocessed:                18
% 1.76/1.00  inst_num_of_loops:                      180
% 1.76/1.00  inst_num_of_learning_restarts:          0
% 1.76/1.00  inst_num_moves_active_passive:          17
% 1.76/1.00  inst_lit_activity:                      0
% 1.76/1.00  inst_lit_activity_moves:                0
% 1.76/1.00  inst_num_tautologies:                   0
% 1.76/1.00  inst_num_prop_implied:                  0
% 1.76/1.00  inst_num_existing_simplified:           0
% 1.76/1.00  inst_num_eq_res_simplified:             0
% 1.76/1.00  inst_num_child_elim:                    0
% 1.76/1.00  inst_num_of_dismatching_blockings:      19
% 1.76/1.00  inst_num_of_non_proper_insts:           184
% 1.76/1.00  inst_num_of_duplicates:                 0
% 1.76/1.00  inst_inst_num_from_inst_to_res:         0
% 1.76/1.00  inst_dismatching_checking_time:         0.
% 1.76/1.00  
% 1.76/1.00  ------ Resolution
% 1.76/1.00  
% 1.76/1.00  res_num_of_clauses:                     0
% 1.76/1.00  res_num_in_passive:                     0
% 1.76/1.00  res_num_in_active:                      0
% 1.76/1.00  res_num_of_loops:                       114
% 1.76/1.00  res_forward_subset_subsumed:            31
% 1.76/1.00  res_backward_subset_subsumed:           2
% 1.76/1.00  res_forward_subsumed:                   0
% 1.76/1.00  res_backward_subsumed:                  0
% 1.76/1.00  res_forward_subsumption_resolution:     10
% 1.76/1.00  res_backward_subsumption_resolution:    3
% 1.76/1.00  res_clause_to_clause_subsumption:       209
% 1.76/1.00  res_orphan_elimination:                 0
% 1.76/1.00  res_tautology_del:                      24
% 1.76/1.00  res_num_eq_res_simplified:              0
% 1.76/1.00  res_num_sel_changes:                    0
% 1.76/1.00  res_moves_from_active_to_pass:          0
% 1.76/1.00  
% 1.76/1.00  ------ Superposition
% 1.76/1.00  
% 1.76/1.00  sup_time_total:                         0.
% 1.76/1.00  sup_time_generating:                    0.
% 1.76/1.00  sup_time_sim_full:                      0.
% 1.76/1.00  sup_time_sim_immed:                     0.
% 1.76/1.00  
% 1.76/1.00  sup_num_of_clauses:                     43
% 1.76/1.00  sup_num_in_active:                      36
% 1.76/1.00  sup_num_in_passive:                     7
% 1.76/1.00  sup_num_of_loops:                       35
% 1.76/1.00  sup_fw_superposition:                   19
% 1.76/1.00  sup_bw_superposition:                   19
% 1.76/1.00  sup_immediate_simplified:               6
% 1.76/1.00  sup_given_eliminated:                   0
% 1.76/1.00  comparisons_done:                       0
% 1.76/1.00  comparisons_avoided:                    0
% 1.76/1.00  
% 1.76/1.00  ------ Simplifications
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  sim_fw_subset_subsumed:                 4
% 1.76/1.00  sim_bw_subset_subsumed:                 0
% 1.76/1.00  sim_fw_subsumed:                        1
% 1.76/1.00  sim_bw_subsumed:                        1
% 1.76/1.00  sim_fw_subsumption_res:                 2
% 1.76/1.00  sim_bw_subsumption_res:                 0
% 1.76/1.00  sim_tautology_del:                      3
% 1.76/1.00  sim_eq_tautology_del:                   5
% 1.76/1.00  sim_eq_res_simp:                        0
% 1.76/1.00  sim_fw_demodulated:                     0
% 1.76/1.00  sim_bw_demodulated:                     0
% 1.76/1.00  sim_light_normalised:                   1
% 1.76/1.00  sim_joinable_taut:                      0
% 1.76/1.00  sim_joinable_simp:                      0
% 1.76/1.00  sim_ac_normalised:                      0
% 1.76/1.00  sim_smt_subsumption:                    0
% 1.76/1.00  
%------------------------------------------------------------------------------
