%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:52 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 570 expanded)
%              Number of clauses        :  106 ( 132 expanded)
%              Number of leaves         :   17 ( 200 expanded)
%              Depth                    :   28
%              Number of atoms          : 1036 (5732 expanded)
%              Number of equality atoms :  108 ( 563 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   24 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
          & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X1,k2_pre_topc(X0,sK7))
        & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = sK7
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f43,f42,f41,f40])).

fof(f73,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
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
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
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
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK0(X0,X1,X2))
                    & r2_hidden(X2,sK0(X0,X1,X2))
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK0(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
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

fof(f65,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK0(X0,X1,X2),X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
        & m1_connsp_2(sK3(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
        & m1_connsp_2(sK2(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f54])).

fof(f70,plain,(
    v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    l1_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK0(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ~ r2_hidden(sK5,k2_pre_topc(sK4,sK7)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2214,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2604,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2214])).

cnf(c_3,plain,
    ( r2_hidden(X0,sK0(X1,X2,X0))
    | r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1177,plain,
    ( r2_hidden(X0,sK0(X1,X2,X0))
    | r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_28])).

cnf(c_1178,plain,
    ( r2_hidden(X0,sK0(sK4,X1,X0))
    | r2_hidden(X0,k2_pre_topc(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1177])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1182,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k2_pre_topc(sK4,X1))
    | r2_hidden(X0,sK0(sK4,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1178,c_30])).

cnf(c_1183,plain,
    ( r2_hidden(X0,sK0(sK4,X1,X0))
    | r2_hidden(X0,k2_pre_topc(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1182])).

cnf(c_2208,plain,
    ( r2_hidden(X0_56,sK0(sK4,X1_56,X0_56))
    | r2_hidden(X0_56,k2_pre_topc(sK4,X1_56))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1183])).

cnf(c_2610,plain,
    ( r2_hidden(X0_56,sK0(sK4,X1_56,X0_56)) = iProver_top
    | r2_hidden(X0_56,k2_pre_topc(sK4,X1_56)) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1153,plain,
    ( r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_1154,plain,
    ( r2_hidden(X0,k2_pre_topc(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1153])).

cnf(c_1158,plain,
    ( m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k2_pre_topc(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1154,c_30])).

cnf(c_1159,plain,
    ( r2_hidden(X0,k2_pre_topc(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1158])).

cnf(c_2209,plain,
    ( r2_hidden(X0_56,k2_pre_topc(sK4,X1_56))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1159])).

cnf(c_2609,plain,
    ( r2_hidden(X0_56,k2_pre_topc(sK4,X1_56)) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK0(sK4,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_868,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_869,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_873,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_30,c_28])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_889,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_873,c_0])).

cnf(c_2211,plain,
    ( m1_connsp_2(X0_56,sK4,X1_56)
    | ~ v3_pre_topc(X0_56,sK4)
    | ~ r2_hidden(X1_56,X0_56)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_889])).

cnf(c_2607,plain,
    ( m1_connsp_2(X0_56,sK4,X1_56) = iProver_top
    | v3_pre_topc(X0_56,sK4) != iProver_top
    | r2_hidden(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2211])).

cnf(c_3402,plain,
    ( m1_connsp_2(sK0(sK4,X0_56,X1_56),sK4,X2_56) = iProver_top
    | v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4) != iProver_top
    | r2_hidden(X2_56,sK0(sK4,X0_56,X1_56)) != iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2609,c_2607])).

cnf(c_4,plain,
    ( v3_pre_topc(sK0(X0,X1,X2),X0)
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1098,plain,
    ( v3_pre_topc(sK0(X0,X1,X2),X0)
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_28])).

cnf(c_1099,plain,
    ( v3_pre_topc(sK0(sK4,X0,X1),sK4)
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1098])).

cnf(c_1103,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | v3_pre_topc(sK0(sK4,X0,X1),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1099,c_30])).

cnf(c_1104,plain,
    ( v3_pre_topc(sK0(sK4,X0,X1),sK4)
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1103])).

cnf(c_2210,plain,
    ( v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4)
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1104])).

cnf(c_2245,plain,
    ( v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4) = iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2210])).

cnf(c_3608,plain,
    ( m1_connsp_2(sK0(sK4,X0_56,X1_56),sK4,X2_56) = iProver_top
    | r2_hidden(X2_56,sK0(sK4,X0_56,X1_56)) != iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3402,c_2245])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2213,negated_conjecture,
    ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2605,plain,
    ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_16,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_796,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_797,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_801,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_797,c_30,c_28])).

cnf(c_15,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_connsp_2(X2,X0,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_572,plain,
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
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_573,plain,
    ( r1_waybel_0(sK4,X0,X1)
    | ~ m1_connsp_2(X1,sK4,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_577,plain,
    ( r1_waybel_0(sK4,X0,X1)
    | ~ m1_connsp_2(X1,sK4,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_30,c_28])).

cnf(c_601,plain,
    ( r1_waybel_0(sK4,X0,X1)
    | ~ m1_connsp_2(X1,sK4,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
    | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_577,c_0])).

cnf(c_819,plain,
    ( r1_waybel_0(sK4,X0,X1)
    | ~ m1_connsp_2(X1,sK4,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_801,c_601])).

cnf(c_24,negated_conjecture,
    ( v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1485,plain,
    ( r1_waybel_0(sK4,X0,X1)
    | ~ m1_connsp_2(X1,sK4,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_819,c_24])).

cnf(c_1486,plain,
    ( r1_waybel_0(sK4,sK6,X0)
    | ~ m1_connsp_2(X0,sK4,X1)
    | ~ l1_waybel_0(sK6,sK4)
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6))
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1485])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( l1_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1490,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK6,X0)
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1486,c_26,c_25,c_23])).

cnf(c_1491,plain,
    ( r1_waybel_0(sK4,sK6,X0)
    | ~ m1_connsp_2(X0,sK4,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_1490])).

cnf(c_2203,plain,
    ( r1_waybel_0(sK4,sK6,X0_56)
    | ~ m1_connsp_2(X0_56,sK4,X1_56)
    | ~ r2_hidden(X1_56,k10_yellow_6(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_1491])).

cnf(c_2615,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) = iProver_top
    | m1_connsp_2(X0_56,sK4,X1_56) != iProver_top
    | r2_hidden(X1_56,k10_yellow_6(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2203])).

cnf(c_3034,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) = iProver_top
    | m1_connsp_2(X0_56,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2605,c_2615])).

cnf(c_3620,plain,
    ( r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56)) = iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | r2_hidden(sK5,sK0(sK4,X0_56,X1_56)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3608,c_3034])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_349,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_17])).

cnf(c_1048,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_349,c_28])).

cnf(c_1049,plain,
    ( ~ r1_waybel_0(sK4,X0,X1)
    | ~ r1_waybel_0(sK4,X0,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r1_xboole_0(X1,X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1048])).

cnf(c_1053,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_xboole_0(X1,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r1_waybel_0(sK4,X0,X2)
    | ~ r1_waybel_0(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_30])).

cnf(c_1054,plain,
    ( ~ r1_waybel_0(sK4,X0,X1)
    | ~ r1_waybel_0(sK4,X0,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r1_xboole_0(X1,X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1053])).

cnf(c_1401,plain,
    ( ~ r1_waybel_0(sK4,X0,X1)
    | ~ r1_waybel_0(sK4,X0,X2)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r1_xboole_0(X1,X2)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1054,c_24])).

cnf(c_1402,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_waybel_0(sK4,sK6,X1)
    | ~ l1_waybel_0(sK6,sK4)
    | ~ r1_xboole_0(X1,X0)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1401])).

cnf(c_1406,plain,
    ( ~ r1_waybel_0(sK4,sK6,X1)
    | ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1402,c_26,c_25,c_23])).

cnf(c_1407,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_waybel_0(sK4,sK6,X1)
    | ~ r1_xboole_0(X0,X1) ),
    inference(renaming,[status(thm)],[c_1406])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,sK0(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1201,plain,
    ( r1_xboole_0(X0,sK0(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_28])).

cnf(c_1202,plain,
    ( r1_xboole_0(X0,sK0(sK4,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1201])).

cnf(c_1206,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | r1_xboole_0(X0,sK0(sK4,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1202,c_30])).

cnf(c_1207,plain,
    ( r1_xboole_0(X0,sK0(sK4,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1206])).

cnf(c_1643,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_waybel_0(sK4,sK6,X1)
    | r2_hidden(X2,k2_pre_topc(sK4,X3))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | X3 != X1
    | sK0(sK4,X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1407,c_1207])).

cnf(c_1644,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0)
    | ~ r1_waybel_0(sK4,sK6,sK0(sK4,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_1643])).

cnf(c_2197,plain,
    ( ~ r1_waybel_0(sK4,sK6,X0_56)
    | ~ r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56))
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1644])).

cnf(c_2621,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
    | r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56)) != iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2197])).

cnf(c_3659,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
    | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
    | r2_hidden(sK5,sK0(sK4,X0_56,X1_56)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3620,c_2621])).

cnf(c_3999,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2610,c_3659])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4004,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
    | r1_waybel_0(sK4,sK6,X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3999,c_34])).

cnf(c_4005,plain,
    ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4004])).

cnf(c_4013,plain,
    ( r1_waybel_0(sK4,sK6,sK7) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK4,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2604,c_4005])).

cnf(c_18,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_329,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_18])).

cnf(c_1079,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_28])).

cnf(c_1080,plain,
    ( r1_waybel_0(sK4,X0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),u1_waybel_0(sK4,X0)))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1079])).

cnf(c_1084,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK4)
    | r1_waybel_0(sK4,X0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),u1_waybel_0(sK4,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1080,c_30])).

cnf(c_1085,plain,
    ( r1_waybel_0(sK4,X0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),u1_waybel_0(sK4,X0)))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1084])).

cnf(c_1630,plain,
    ( r1_waybel_0(sK4,X0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),u1_waybel_0(sK4,X0)))
    | v2_struct_0(X0)
    | sK6 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1085])).

cnf(c_1631,plain,
    ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1630])).

cnf(c_1633,plain,
    ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1631,c_26])).

cnf(c_2198,plain,
    ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) ),
    inference(subtyping,[status(esa)],[c_1633])).

cnf(c_2620,plain,
    ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2198])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2215,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2634,plain,
    ( r1_waybel_0(sK4,sK6,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2620,c_2215])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(sK5,k2_pre_topc(sK4,sK7)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_41,plain,
    ( r2_hidden(sK5,k2_pre_topc(sK4,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4013,c_2634,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:59:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.65/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.65/1.00  
% 1.65/1.00  ------  iProver source info
% 1.65/1.00  
% 1.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.65/1.00  git: non_committed_changes: false
% 1.65/1.00  git: last_make_outside_of_git: false
% 1.65/1.00  
% 1.65/1.00  ------ 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options
% 1.65/1.00  
% 1.65/1.00  --out_options                           all
% 1.65/1.00  --tptp_safe_out                         true
% 1.65/1.00  --problem_path                          ""
% 1.65/1.00  --include_path                          ""
% 1.65/1.00  --clausifier                            res/vclausify_rel
% 1.65/1.00  --clausifier_options                    --mode clausify
% 1.65/1.00  --stdin                                 false
% 1.65/1.00  --stats_out                             all
% 1.65/1.00  
% 1.65/1.00  ------ General Options
% 1.65/1.00  
% 1.65/1.00  --fof                                   false
% 1.65/1.00  --time_out_real                         305.
% 1.65/1.00  --time_out_virtual                      -1.
% 1.65/1.00  --symbol_type_check                     false
% 1.65/1.00  --clausify_out                          false
% 1.65/1.00  --sig_cnt_out                           false
% 1.65/1.00  --trig_cnt_out                          false
% 1.65/1.00  --trig_cnt_out_tolerance                1.
% 1.65/1.00  --trig_cnt_out_sk_spl                   false
% 1.65/1.00  --abstr_cl_out                          false
% 1.65/1.00  
% 1.65/1.00  ------ Global Options
% 1.65/1.00  
% 1.65/1.00  --schedule                              default
% 1.65/1.00  --add_important_lit                     false
% 1.65/1.00  --prop_solver_per_cl                    1000
% 1.65/1.00  --min_unsat_core                        false
% 1.65/1.00  --soft_assumptions                      false
% 1.65/1.00  --soft_lemma_size                       3
% 1.65/1.00  --prop_impl_unit_size                   0
% 1.65/1.00  --prop_impl_unit                        []
% 1.65/1.00  --share_sel_clauses                     true
% 1.65/1.00  --reset_solvers                         false
% 1.65/1.00  --bc_imp_inh                            [conj_cone]
% 1.65/1.00  --conj_cone_tolerance                   3.
% 1.65/1.00  --extra_neg_conj                        none
% 1.65/1.00  --large_theory_mode                     true
% 1.65/1.00  --prolific_symb_bound                   200
% 1.65/1.00  --lt_threshold                          2000
% 1.65/1.00  --clause_weak_htbl                      true
% 1.65/1.00  --gc_record_bc_elim                     false
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing Options
% 1.65/1.00  
% 1.65/1.00  --preprocessing_flag                    true
% 1.65/1.00  --time_out_prep_mult                    0.1
% 1.65/1.00  --splitting_mode                        input
% 1.65/1.00  --splitting_grd                         true
% 1.65/1.00  --splitting_cvd                         false
% 1.65/1.00  --splitting_cvd_svl                     false
% 1.65/1.00  --splitting_nvd                         32
% 1.65/1.00  --sub_typing                            true
% 1.65/1.00  --prep_gs_sim                           true
% 1.65/1.00  --prep_unflatten                        true
% 1.65/1.00  --prep_res_sim                          true
% 1.65/1.00  --prep_upred                            true
% 1.65/1.00  --prep_sem_filter                       exhaustive
% 1.65/1.00  --prep_sem_filter_out                   false
% 1.65/1.00  --pred_elim                             true
% 1.65/1.00  --res_sim_input                         true
% 1.65/1.00  --eq_ax_congr_red                       true
% 1.65/1.00  --pure_diseq_elim                       true
% 1.65/1.00  --brand_transform                       false
% 1.65/1.00  --non_eq_to_eq                          false
% 1.65/1.00  --prep_def_merge                        true
% 1.65/1.00  --prep_def_merge_prop_impl              false
% 1.65/1.00  --prep_def_merge_mbd                    true
% 1.65/1.00  --prep_def_merge_tr_red                 false
% 1.65/1.00  --prep_def_merge_tr_cl                  false
% 1.65/1.00  --smt_preprocessing                     true
% 1.65/1.00  --smt_ac_axioms                         fast
% 1.65/1.00  --preprocessed_out                      false
% 1.65/1.00  --preprocessed_stats                    false
% 1.65/1.00  
% 1.65/1.00  ------ Abstraction refinement Options
% 1.65/1.00  
% 1.65/1.00  --abstr_ref                             []
% 1.65/1.00  --abstr_ref_prep                        false
% 1.65/1.00  --abstr_ref_until_sat                   false
% 1.65/1.00  --abstr_ref_sig_restrict                funpre
% 1.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/1.00  --abstr_ref_under                       []
% 1.65/1.00  
% 1.65/1.00  ------ SAT Options
% 1.65/1.00  
% 1.65/1.00  --sat_mode                              false
% 1.65/1.00  --sat_fm_restart_options                ""
% 1.65/1.00  --sat_gr_def                            false
% 1.65/1.00  --sat_epr_types                         true
% 1.65/1.00  --sat_non_cyclic_types                  false
% 1.65/1.00  --sat_finite_models                     false
% 1.65/1.00  --sat_fm_lemmas                         false
% 1.65/1.00  --sat_fm_prep                           false
% 1.65/1.00  --sat_fm_uc_incr                        true
% 1.65/1.00  --sat_out_model                         small
% 1.65/1.00  --sat_out_clauses                       false
% 1.65/1.00  
% 1.65/1.00  ------ QBF Options
% 1.65/1.00  
% 1.65/1.00  --qbf_mode                              false
% 1.65/1.00  --qbf_elim_univ                         false
% 1.65/1.00  --qbf_dom_inst                          none
% 1.65/1.00  --qbf_dom_pre_inst                      false
% 1.65/1.00  --qbf_sk_in                             false
% 1.65/1.00  --qbf_pred_elim                         true
% 1.65/1.00  --qbf_split                             512
% 1.65/1.00  
% 1.65/1.00  ------ BMC1 Options
% 1.65/1.00  
% 1.65/1.00  --bmc1_incremental                      false
% 1.65/1.00  --bmc1_axioms                           reachable_all
% 1.65/1.00  --bmc1_min_bound                        0
% 1.65/1.00  --bmc1_max_bound                        -1
% 1.65/1.00  --bmc1_max_bound_default                -1
% 1.65/1.00  --bmc1_symbol_reachability              true
% 1.65/1.00  --bmc1_property_lemmas                  false
% 1.65/1.00  --bmc1_k_induction                      false
% 1.65/1.00  --bmc1_non_equiv_states                 false
% 1.65/1.00  --bmc1_deadlock                         false
% 1.65/1.00  --bmc1_ucm                              false
% 1.65/1.00  --bmc1_add_unsat_core                   none
% 1.65/1.00  --bmc1_unsat_core_children              false
% 1.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/1.00  --bmc1_out_stat                         full
% 1.65/1.00  --bmc1_ground_init                      false
% 1.65/1.00  --bmc1_pre_inst_next_state              false
% 1.65/1.00  --bmc1_pre_inst_state                   false
% 1.65/1.00  --bmc1_pre_inst_reach_state             false
% 1.65/1.00  --bmc1_out_unsat_core                   false
% 1.65/1.00  --bmc1_aig_witness_out                  false
% 1.65/1.00  --bmc1_verbose                          false
% 1.65/1.00  --bmc1_dump_clauses_tptp                false
% 1.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.65/1.00  --bmc1_dump_file                        -
% 1.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.65/1.00  --bmc1_ucm_extend_mode                  1
% 1.65/1.00  --bmc1_ucm_init_mode                    2
% 1.65/1.00  --bmc1_ucm_cone_mode                    none
% 1.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.65/1.00  --bmc1_ucm_relax_model                  4
% 1.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/1.00  --bmc1_ucm_layered_model                none
% 1.65/1.00  --bmc1_ucm_max_lemma_size               10
% 1.65/1.00  
% 1.65/1.00  ------ AIG Options
% 1.65/1.00  
% 1.65/1.00  --aig_mode                              false
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation Options
% 1.65/1.00  
% 1.65/1.00  --instantiation_flag                    true
% 1.65/1.00  --inst_sos_flag                         false
% 1.65/1.00  --inst_sos_phase                        true
% 1.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel_side                     num_symb
% 1.65/1.00  --inst_solver_per_active                1400
% 1.65/1.00  --inst_solver_calls_frac                1.
% 1.65/1.00  --inst_passive_queue_type               priority_queues
% 1.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/1.00  --inst_passive_queues_freq              [25;2]
% 1.65/1.00  --inst_dismatching                      true
% 1.65/1.00  --inst_eager_unprocessed_to_passive     true
% 1.65/1.00  --inst_prop_sim_given                   true
% 1.65/1.00  --inst_prop_sim_new                     false
% 1.65/1.00  --inst_subs_new                         false
% 1.65/1.00  --inst_eq_res_simp                      false
% 1.65/1.00  --inst_subs_given                       false
% 1.65/1.00  --inst_orphan_elimination               true
% 1.65/1.00  --inst_learning_loop_flag               true
% 1.65/1.00  --inst_learning_start                   3000
% 1.65/1.00  --inst_learning_factor                  2
% 1.65/1.00  --inst_start_prop_sim_after_learn       3
% 1.65/1.00  --inst_sel_renew                        solver
% 1.65/1.00  --inst_lit_activity_flag                true
% 1.65/1.00  --inst_restr_to_given                   false
% 1.65/1.00  --inst_activity_threshold               500
% 1.65/1.00  --inst_out_proof                        true
% 1.65/1.00  
% 1.65/1.00  ------ Resolution Options
% 1.65/1.00  
% 1.65/1.00  --resolution_flag                       true
% 1.65/1.00  --res_lit_sel                           adaptive
% 1.65/1.00  --res_lit_sel_side                      none
% 1.65/1.00  --res_ordering                          kbo
% 1.65/1.00  --res_to_prop_solver                    active
% 1.65/1.00  --res_prop_simpl_new                    false
% 1.65/1.00  --res_prop_simpl_given                  true
% 1.65/1.00  --res_passive_queue_type                priority_queues
% 1.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/1.00  --res_passive_queues_freq               [15;5]
% 1.65/1.00  --res_forward_subs                      full
% 1.65/1.00  --res_backward_subs                     full
% 1.65/1.00  --res_forward_subs_resolution           true
% 1.65/1.00  --res_backward_subs_resolution          true
% 1.65/1.00  --res_orphan_elimination                true
% 1.65/1.00  --res_time_limit                        2.
% 1.65/1.00  --res_out_proof                         true
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Options
% 1.65/1.00  
% 1.65/1.00  --superposition_flag                    true
% 1.65/1.00  --sup_passive_queue_type                priority_queues
% 1.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.65/1.00  --demod_completeness_check              fast
% 1.65/1.00  --demod_use_ground                      true
% 1.65/1.00  --sup_to_prop_solver                    passive
% 1.65/1.00  --sup_prop_simpl_new                    true
% 1.65/1.00  --sup_prop_simpl_given                  true
% 1.65/1.00  --sup_fun_splitting                     false
% 1.65/1.00  --sup_smt_interval                      50000
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Simplification Setup
% 1.65/1.00  
% 1.65/1.00  --sup_indices_passive                   []
% 1.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_full_bw                           [BwDemod]
% 1.65/1.00  --sup_immed_triv                        [TrivRules]
% 1.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_immed_bw_main                     []
% 1.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  
% 1.65/1.00  ------ Combination Options
% 1.65/1.00  
% 1.65/1.00  --comb_res_mult                         3
% 1.65/1.00  --comb_sup_mult                         2
% 1.65/1.00  --comb_inst_mult                        10
% 1.65/1.00  
% 1.65/1.00  ------ Debug Options
% 1.65/1.00  
% 1.65/1.00  --dbg_backtrace                         false
% 1.65/1.00  --dbg_dump_prop_clauses                 false
% 1.65/1.00  --dbg_dump_prop_clauses_file            -
% 1.65/1.00  --dbg_out_stat                          false
% 1.65/1.00  ------ Parsing...
% 1.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.65/1.00  ------ Proving...
% 1.65/1.00  ------ Problem Properties 
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  clauses                                 21
% 1.65/1.00  conjectures                             5
% 1.65/1.00  EPR                                     0
% 1.65/1.00  Horn                                    14
% 1.65/1.00  unary                                   7
% 1.65/1.00  binary                                  0
% 1.65/1.00  lits                                    61
% 1.65/1.00  lits eq                                 5
% 1.65/1.00  fd_pure                                 0
% 1.65/1.00  fd_pseudo                               0
% 1.65/1.00  fd_cond                                 4
% 1.65/1.00  fd_pseudo_cond                          0
% 1.65/1.00  AC symbols                              0
% 1.65/1.00  
% 1.65/1.00  ------ Schedule dynamic 5 is on 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  ------ 
% 1.65/1.00  Current options:
% 1.65/1.00  ------ 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options
% 1.65/1.00  
% 1.65/1.00  --out_options                           all
% 1.65/1.00  --tptp_safe_out                         true
% 1.65/1.00  --problem_path                          ""
% 1.65/1.00  --include_path                          ""
% 1.65/1.00  --clausifier                            res/vclausify_rel
% 1.65/1.00  --clausifier_options                    --mode clausify
% 1.65/1.00  --stdin                                 false
% 1.65/1.00  --stats_out                             all
% 1.65/1.00  
% 1.65/1.00  ------ General Options
% 1.65/1.00  
% 1.65/1.00  --fof                                   false
% 1.65/1.00  --time_out_real                         305.
% 1.65/1.00  --time_out_virtual                      -1.
% 1.65/1.00  --symbol_type_check                     false
% 1.65/1.00  --clausify_out                          false
% 1.65/1.00  --sig_cnt_out                           false
% 1.65/1.00  --trig_cnt_out                          false
% 1.65/1.00  --trig_cnt_out_tolerance                1.
% 1.65/1.00  --trig_cnt_out_sk_spl                   false
% 1.65/1.00  --abstr_cl_out                          false
% 1.65/1.00  
% 1.65/1.00  ------ Global Options
% 1.65/1.00  
% 1.65/1.00  --schedule                              default
% 1.65/1.00  --add_important_lit                     false
% 1.65/1.00  --prop_solver_per_cl                    1000
% 1.65/1.00  --min_unsat_core                        false
% 1.65/1.00  --soft_assumptions                      false
% 1.65/1.00  --soft_lemma_size                       3
% 1.65/1.00  --prop_impl_unit_size                   0
% 1.65/1.00  --prop_impl_unit                        []
% 1.65/1.00  --share_sel_clauses                     true
% 1.65/1.00  --reset_solvers                         false
% 1.65/1.00  --bc_imp_inh                            [conj_cone]
% 1.65/1.00  --conj_cone_tolerance                   3.
% 1.65/1.00  --extra_neg_conj                        none
% 1.65/1.00  --large_theory_mode                     true
% 1.65/1.00  --prolific_symb_bound                   200
% 1.65/1.00  --lt_threshold                          2000
% 1.65/1.00  --clause_weak_htbl                      true
% 1.65/1.00  --gc_record_bc_elim                     false
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing Options
% 1.65/1.00  
% 1.65/1.00  --preprocessing_flag                    true
% 1.65/1.00  --time_out_prep_mult                    0.1
% 1.65/1.00  --splitting_mode                        input
% 1.65/1.00  --splitting_grd                         true
% 1.65/1.00  --splitting_cvd                         false
% 1.65/1.00  --splitting_cvd_svl                     false
% 1.65/1.00  --splitting_nvd                         32
% 1.65/1.00  --sub_typing                            true
% 1.65/1.00  --prep_gs_sim                           true
% 1.65/1.00  --prep_unflatten                        true
% 1.65/1.00  --prep_res_sim                          true
% 1.65/1.00  --prep_upred                            true
% 1.65/1.00  --prep_sem_filter                       exhaustive
% 1.65/1.00  --prep_sem_filter_out                   false
% 1.65/1.00  --pred_elim                             true
% 1.65/1.00  --res_sim_input                         true
% 1.65/1.00  --eq_ax_congr_red                       true
% 1.65/1.00  --pure_diseq_elim                       true
% 1.65/1.00  --brand_transform                       false
% 1.65/1.00  --non_eq_to_eq                          false
% 1.65/1.00  --prep_def_merge                        true
% 1.65/1.00  --prep_def_merge_prop_impl              false
% 1.65/1.00  --prep_def_merge_mbd                    true
% 1.65/1.00  --prep_def_merge_tr_red                 false
% 1.65/1.00  --prep_def_merge_tr_cl                  false
% 1.65/1.00  --smt_preprocessing                     true
% 1.65/1.00  --smt_ac_axioms                         fast
% 1.65/1.00  --preprocessed_out                      false
% 1.65/1.00  --preprocessed_stats                    false
% 1.65/1.00  
% 1.65/1.00  ------ Abstraction refinement Options
% 1.65/1.00  
% 1.65/1.00  --abstr_ref                             []
% 1.65/1.00  --abstr_ref_prep                        false
% 1.65/1.00  --abstr_ref_until_sat                   false
% 1.65/1.00  --abstr_ref_sig_restrict                funpre
% 1.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/1.00  --abstr_ref_under                       []
% 1.65/1.00  
% 1.65/1.00  ------ SAT Options
% 1.65/1.00  
% 1.65/1.00  --sat_mode                              false
% 1.65/1.00  --sat_fm_restart_options                ""
% 1.65/1.00  --sat_gr_def                            false
% 1.65/1.00  --sat_epr_types                         true
% 1.65/1.00  --sat_non_cyclic_types                  false
% 1.65/1.00  --sat_finite_models                     false
% 1.65/1.00  --sat_fm_lemmas                         false
% 1.65/1.00  --sat_fm_prep                           false
% 1.65/1.00  --sat_fm_uc_incr                        true
% 1.65/1.00  --sat_out_model                         small
% 1.65/1.00  --sat_out_clauses                       false
% 1.65/1.00  
% 1.65/1.00  ------ QBF Options
% 1.65/1.00  
% 1.65/1.00  --qbf_mode                              false
% 1.65/1.00  --qbf_elim_univ                         false
% 1.65/1.00  --qbf_dom_inst                          none
% 1.65/1.00  --qbf_dom_pre_inst                      false
% 1.65/1.00  --qbf_sk_in                             false
% 1.65/1.00  --qbf_pred_elim                         true
% 1.65/1.00  --qbf_split                             512
% 1.65/1.00  
% 1.65/1.00  ------ BMC1 Options
% 1.65/1.00  
% 1.65/1.00  --bmc1_incremental                      false
% 1.65/1.00  --bmc1_axioms                           reachable_all
% 1.65/1.00  --bmc1_min_bound                        0
% 1.65/1.00  --bmc1_max_bound                        -1
% 1.65/1.00  --bmc1_max_bound_default                -1
% 1.65/1.00  --bmc1_symbol_reachability              true
% 1.65/1.00  --bmc1_property_lemmas                  false
% 1.65/1.00  --bmc1_k_induction                      false
% 1.65/1.00  --bmc1_non_equiv_states                 false
% 1.65/1.00  --bmc1_deadlock                         false
% 1.65/1.00  --bmc1_ucm                              false
% 1.65/1.00  --bmc1_add_unsat_core                   none
% 1.65/1.00  --bmc1_unsat_core_children              false
% 1.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/1.00  --bmc1_out_stat                         full
% 1.65/1.00  --bmc1_ground_init                      false
% 1.65/1.00  --bmc1_pre_inst_next_state              false
% 1.65/1.00  --bmc1_pre_inst_state                   false
% 1.65/1.00  --bmc1_pre_inst_reach_state             false
% 1.65/1.00  --bmc1_out_unsat_core                   false
% 1.65/1.00  --bmc1_aig_witness_out                  false
% 1.65/1.00  --bmc1_verbose                          false
% 1.65/1.00  --bmc1_dump_clauses_tptp                false
% 1.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.65/1.00  --bmc1_dump_file                        -
% 1.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.65/1.00  --bmc1_ucm_extend_mode                  1
% 1.65/1.00  --bmc1_ucm_init_mode                    2
% 1.65/1.00  --bmc1_ucm_cone_mode                    none
% 1.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.65/1.00  --bmc1_ucm_relax_model                  4
% 1.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/1.00  --bmc1_ucm_layered_model                none
% 1.65/1.00  --bmc1_ucm_max_lemma_size               10
% 1.65/1.00  
% 1.65/1.00  ------ AIG Options
% 1.65/1.00  
% 1.65/1.00  --aig_mode                              false
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation Options
% 1.65/1.00  
% 1.65/1.00  --instantiation_flag                    true
% 1.65/1.00  --inst_sos_flag                         false
% 1.65/1.00  --inst_sos_phase                        true
% 1.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel_side                     none
% 1.65/1.00  --inst_solver_per_active                1400
% 1.65/1.00  --inst_solver_calls_frac                1.
% 1.65/1.00  --inst_passive_queue_type               priority_queues
% 1.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/1.00  --inst_passive_queues_freq              [25;2]
% 1.65/1.00  --inst_dismatching                      true
% 1.65/1.00  --inst_eager_unprocessed_to_passive     true
% 1.65/1.00  --inst_prop_sim_given                   true
% 1.65/1.00  --inst_prop_sim_new                     false
% 1.65/1.00  --inst_subs_new                         false
% 1.65/1.00  --inst_eq_res_simp                      false
% 1.65/1.00  --inst_subs_given                       false
% 1.65/1.00  --inst_orphan_elimination               true
% 1.65/1.00  --inst_learning_loop_flag               true
% 1.65/1.00  --inst_learning_start                   3000
% 1.65/1.00  --inst_learning_factor                  2
% 1.65/1.00  --inst_start_prop_sim_after_learn       3
% 1.65/1.00  --inst_sel_renew                        solver
% 1.65/1.00  --inst_lit_activity_flag                true
% 1.65/1.00  --inst_restr_to_given                   false
% 1.65/1.00  --inst_activity_threshold               500
% 1.65/1.00  --inst_out_proof                        true
% 1.65/1.00  
% 1.65/1.00  ------ Resolution Options
% 1.65/1.00  
% 1.65/1.00  --resolution_flag                       false
% 1.65/1.00  --res_lit_sel                           adaptive
% 1.65/1.00  --res_lit_sel_side                      none
% 1.65/1.00  --res_ordering                          kbo
% 1.65/1.00  --res_to_prop_solver                    active
% 1.65/1.00  --res_prop_simpl_new                    false
% 1.65/1.00  --res_prop_simpl_given                  true
% 1.65/1.00  --res_passive_queue_type                priority_queues
% 1.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/1.00  --res_passive_queues_freq               [15;5]
% 1.65/1.00  --res_forward_subs                      full
% 1.65/1.00  --res_backward_subs                     full
% 1.65/1.00  --res_forward_subs_resolution           true
% 1.65/1.00  --res_backward_subs_resolution          true
% 1.65/1.00  --res_orphan_elimination                true
% 1.65/1.00  --res_time_limit                        2.
% 1.65/1.00  --res_out_proof                         true
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Options
% 1.65/1.00  
% 1.65/1.00  --superposition_flag                    true
% 1.65/1.00  --sup_passive_queue_type                priority_queues
% 1.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.65/1.00  --demod_completeness_check              fast
% 1.65/1.00  --demod_use_ground                      true
% 1.65/1.00  --sup_to_prop_solver                    passive
% 1.65/1.00  --sup_prop_simpl_new                    true
% 1.65/1.00  --sup_prop_simpl_given                  true
% 1.65/1.00  --sup_fun_splitting                     false
% 1.65/1.00  --sup_smt_interval                      50000
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Simplification Setup
% 1.65/1.00  
% 1.65/1.00  --sup_indices_passive                   []
% 1.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_full_bw                           [BwDemod]
% 1.65/1.00  --sup_immed_triv                        [TrivRules]
% 1.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_immed_bw_main                     []
% 1.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  
% 1.65/1.00  ------ Combination Options
% 1.65/1.00  
% 1.65/1.00  --comb_res_mult                         3
% 1.65/1.00  --comb_sup_mult                         2
% 1.65/1.00  --comb_inst_mult                        10
% 1.65/1.00  
% 1.65/1.00  ------ Debug Options
% 1.65/1.00  
% 1.65/1.00  --dbg_backtrace                         false
% 1.65/1.00  --dbg_dump_prop_clauses                 false
% 1.65/1.00  --dbg_dump_prop_clauses_file            -
% 1.65/1.00  --dbg_out_stat                          false
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  ------ Proving...
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  % SZS status Theorem for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  fof(f9,conjecture,(
% 1.65/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f10,negated_conjecture,(
% 1.65/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 1.65/1.00    inference(negated_conjecture,[],[f9])).
% 1.65/1.00  
% 1.65/1.00  fof(f26,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f10])).
% 1.65/1.00  
% 1.65/1.00  fof(f27,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f26])).
% 1.65/1.00  
% 1.65/1.00  fof(f43,plain,(
% 1.65/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X1,k2_pre_topc(X0,sK7)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = sK7 & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f42,plain,(
% 1.65/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(X0),u1_waybel_0(X0,sK6)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,sK6)) & l1_waybel_0(sK6,X0) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6))) )),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f41,plain,(
% 1.65/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~r2_hidden(sK5,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK5,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f40,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(sK4,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK4),u1_waybel_0(sK4,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X1,k10_yellow_6(sK4,X2)) & l1_waybel_0(X2,sK4) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f44,plain,(
% 1.65/1.00    (((~r2_hidden(sK5,k2_pre_topc(sK4,sK7)) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK5,k10_yellow_6(sK4,sK6)) & l1_waybel_0(sK6,sK4) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f43,f42,f41,f40])).
% 1.65/1.00  
% 1.65/1.00  fof(f73,plain,(
% 1.65/1.00    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f3,axiom,(
% 1.65/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f14,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(ennf_transformation,[],[f3])).
% 1.65/1.00  
% 1.65/1.00  fof(f15,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(flattening,[],[f14])).
% 1.65/1.00  
% 1.65/1.00  fof(f28,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(nnf_transformation,[],[f15])).
% 1.65/1.00  
% 1.65/1.00  fof(f29,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(flattening,[],[f28])).
% 1.65/1.00  
% 1.65/1.00  fof(f30,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(rectify,[],[f29])).
% 1.65/1.00  
% 1.65/1.00  fof(f31,plain,(
% 1.65/1.00    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK0(X0,X1,X2)) & r2_hidden(X2,sK0(X0,X1,X2)) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f32,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK0(X0,X1,X2)) & r2_hidden(X2,sK0(X0,X1,X2)) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 1.65/1.00  
% 1.65/1.00  fof(f51,plain,(
% 1.65/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r2_hidden(X2,sK0(X0,X1,X2)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f32])).
% 1.65/1.00  
% 1.65/1.00  fof(f66,plain,(
% 1.65/1.00    l1_pre_topc(sK4)),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f64,plain,(
% 1.65/1.00    ~v2_struct_0(sK4)),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f49,plain,(
% 1.65/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f32])).
% 1.65/1.00  
% 1.65/1.00  fof(f4,axiom,(
% 1.65/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f16,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f4])).
% 1.65/1.00  
% 1.65/1.00  fof(f17,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f16])).
% 1.65/1.00  
% 1.65/1.00  fof(f53,plain,(
% 1.65/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f17])).
% 1.65/1.00  
% 1.65/1.00  fof(f65,plain,(
% 1.65/1.00    v2_pre_topc(sK4)),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f1,axiom,(
% 1.65/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f11,plain,(
% 1.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.65/1.00    inference(ennf_transformation,[],[f1])).
% 1.65/1.00  
% 1.65/1.00  fof(f12,plain,(
% 1.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.65/1.00    inference(flattening,[],[f11])).
% 1.65/1.00  
% 1.65/1.00  fof(f45,plain,(
% 1.65/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f12])).
% 1.65/1.00  
% 1.65/1.00  fof(f50,plain,(
% 1.65/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | v3_pre_topc(sK0(X0,X1,X2),X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f32])).
% 1.65/1.00  
% 1.65/1.00  fof(f72,plain,(
% 1.65/1.00    r2_hidden(sK5,k10_yellow_6(sK4,sK6))),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f6,axiom,(
% 1.65/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f20,plain,(
% 1.65/1.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f6])).
% 1.65/1.00  
% 1.65/1.00  fof(f21,plain,(
% 1.65/1.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f20])).
% 1.65/1.00  
% 1.65/1.00  fof(f61,plain,(
% 1.65/1.00    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f21])).
% 1.65/1.00  
% 1.65/1.00  fof(f5,axiom,(
% 1.65/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f18,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f5])).
% 1.65/1.00  
% 1.65/1.00  fof(f19,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f18])).
% 1.65/1.00  
% 1.65/1.00  fof(f33,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(nnf_transformation,[],[f19])).
% 1.65/1.00  
% 1.65/1.00  fof(f34,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f33])).
% 1.65/1.00  
% 1.65/1.00  fof(f35,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(rectify,[],[f34])).
% 1.65/1.00  
% 1.65/1.00  fof(f38,plain,(
% 1.65/1.00    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6)))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f37,plain,(
% 1.65/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,X3)))) )),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f36,plain,(
% 1.65/1.00    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f39,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 1.65/1.00  
% 1.65/1.00  fof(f54,plain,(
% 1.65/1.00    ( ! [X6,X2,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f39])).
% 1.65/1.00  
% 1.65/1.00  fof(f78,plain,(
% 1.65/1.00    ( ! [X6,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(equality_resolution,[],[f54])).
% 1.65/1.00  
% 1.65/1.00  fof(f70,plain,(
% 1.65/1.00    v7_waybel_0(sK6)),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f68,plain,(
% 1.65/1.00    ~v2_struct_0(sK6)),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f69,plain,(
% 1.65/1.00    v4_orders_2(sK6)),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f71,plain,(
% 1.65/1.00    l1_waybel_0(sK6,sK4)),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f2,axiom,(
% 1.65/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f13,plain,(
% 1.65/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(ennf_transformation,[],[f2])).
% 1.65/1.00  
% 1.65/1.00  fof(f46,plain,(
% 1.65/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f13])).
% 1.65/1.00  
% 1.65/1.00  fof(f7,axiom,(
% 1.65/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f22,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f7])).
% 1.65/1.00  
% 1.65/1.00  fof(f23,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f22])).
% 1.65/1.00  
% 1.65/1.00  fof(f62,plain,(
% 1.65/1.00    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f23])).
% 1.65/1.00  
% 1.65/1.00  fof(f52,plain,(
% 1.65/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_xboole_0(X1,sK0(X0,X1,X2)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f32])).
% 1.65/1.00  
% 1.65/1.00  fof(f67,plain,(
% 1.65/1.00    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f8,axiom,(
% 1.65/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 1.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f24,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f8])).
% 1.65/1.00  
% 1.65/1.00  fof(f25,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f24])).
% 1.65/1.00  
% 1.65/1.00  fof(f63,plain,(
% 1.65/1.00    ( ! [X0,X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f25])).
% 1.65/1.00  
% 1.65/1.00  fof(f74,plain,(
% 1.65/1.00    k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  fof(f75,plain,(
% 1.65/1.00    ~r2_hidden(sK5,k2_pre_topc(sK4,sK7))),
% 1.65/1.00    inference(cnf_transformation,[],[f44])).
% 1.65/1.00  
% 1.65/1.00  cnf(c_21,negated_conjecture,
% 1.65/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2214,negated_conjecture,
% 1.65/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2604,plain,
% 1.65/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2214]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3,plain,
% 1.65/1.00      ( r2_hidden(X0,sK0(X1,X2,X0))
% 1.65/1.00      | r2_hidden(X0,k2_pre_topc(X1,X2))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_28,negated_conjecture,
% 1.65/1.00      ( l1_pre_topc(sK4) ),
% 1.65/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1177,plain,
% 1.65/1.00      ( r2_hidden(X0,sK0(X1,X2,X0))
% 1.65/1.00      | r2_hidden(X0,k2_pre_topc(X1,X2))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | sK4 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1178,plain,
% 1.65/1.00      ( r2_hidden(X0,sK0(sK4,X1,X0))
% 1.65/1.00      | r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | v2_struct_0(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1177]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_30,negated_conjecture,
% 1.65/1.00      ( ~ v2_struct_0(sK4) ),
% 1.65/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1182,plain,
% 1.65/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.65/1.00      | r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.65/1.00      | r2_hidden(X0,sK0(sK4,X1,X0)) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1178,c_30]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1183,plain,
% 1.65/1.00      ( r2_hidden(X0,sK0(sK4,X1,X0))
% 1.65/1.00      | r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_1182]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2208,plain,
% 1.65/1.00      ( r2_hidden(X0_56,sK0(sK4,X1_56,X0_56))
% 1.65/1.00      | r2_hidden(X0_56,k2_pre_topc(sK4,X1_56))
% 1.65/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_1183]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2610,plain,
% 1.65/1.00      ( r2_hidden(X0_56,sK0(sK4,X1_56,X0_56)) = iProver_top
% 1.65/1.00      | r2_hidden(X0_56,k2_pre_topc(sK4,X1_56)) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_5,plain,
% 1.65/1.00      ( r2_hidden(X0,k2_pre_topc(X1,X2))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1153,plain,
% 1.65/1.00      ( r2_hidden(X0,k2_pre_topc(X1,X2))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | sK4 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1154,plain,
% 1.65/1.00      ( r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | v2_struct_0(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1153]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1158,plain,
% 1.65/1.00      ( m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.65/1.00      | r2_hidden(X0,k2_pre_topc(sK4,X1)) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1154,c_30]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1159,plain,
% 1.65/1.00      ( r2_hidden(X0,k2_pre_topc(sK4,X1))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | m1_subset_1(sK0(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_1158]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2209,plain,
% 1.65/1.00      ( r2_hidden(X0_56,k2_pre_topc(sK4,X1_56))
% 1.65/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | m1_subset_1(sK0(sK4,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_1159]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2609,plain,
% 1.65/1.00      ( r2_hidden(X0_56,k2_pre_topc(sK4,X1_56)) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.65/1.00      | m1_subset_1(sK0(sK4,X1_56,X0_56),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2209]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_8,plain,
% 1.65/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.65/1.00      | ~ v3_pre_topc(X0,X1)
% 1.65/1.00      | ~ r2_hidden(X2,X0)
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_pre_topc(X1)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_29,negated_conjecture,
% 1.65/1.00      ( v2_pre_topc(sK4) ),
% 1.65/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_868,plain,
% 1.65/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.65/1.00      | ~ v3_pre_topc(X0,X1)
% 1.65/1.00      | ~ r2_hidden(X2,X0)
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | sK4 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_869,plain,
% 1.65/1.00      ( m1_connsp_2(X0,sK4,X1)
% 1.65/1.00      | ~ v3_pre_topc(X0,sK4)
% 1.65/1.00      | ~ r2_hidden(X1,X0)
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | v2_struct_0(sK4)
% 1.65/1.00      | ~ l1_pre_topc(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_868]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_873,plain,
% 1.65/1.00      ( m1_connsp_2(X0,sK4,X1)
% 1.65/1.00      | ~ v3_pre_topc(X0,sK4)
% 1.65/1.00      | ~ r2_hidden(X1,X0)
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_869,c_30,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_0,plain,
% 1.65/1.00      ( ~ r2_hidden(X0,X1)
% 1.65/1.00      | m1_subset_1(X0,X2)
% 1.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 1.65/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_889,plain,
% 1.65/1.00      ( m1_connsp_2(X0,sK4,X1)
% 1.65/1.00      | ~ v3_pre_topc(X0,sK4)
% 1.65/1.00      | ~ r2_hidden(X1,X0)
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_873,c_0]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2211,plain,
% 1.65/1.00      ( m1_connsp_2(X0_56,sK4,X1_56)
% 1.65/1.00      | ~ v3_pre_topc(X0_56,sK4)
% 1.65/1.00      | ~ r2_hidden(X1_56,X0_56)
% 1.65/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_889]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2607,plain,
% 1.65/1.00      ( m1_connsp_2(X0_56,sK4,X1_56) = iProver_top
% 1.65/1.00      | v3_pre_topc(X0_56,sK4) != iProver_top
% 1.65/1.00      | r2_hidden(X1_56,X0_56) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2211]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3402,plain,
% 1.65/1.00      ( m1_connsp_2(sK0(sK4,X0_56,X1_56),sK4,X2_56) = iProver_top
% 1.65/1.00      | v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4) != iProver_top
% 1.65/1.00      | r2_hidden(X2_56,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.65/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_2609,c_2607]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_4,plain,
% 1.65/1.00      ( v3_pre_topc(sK0(X0,X1,X2),X0)
% 1.65/1.00      | r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | ~ l1_pre_topc(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1098,plain,
% 1.65/1.00      ( v3_pre_topc(sK0(X0,X1,X2),X0)
% 1.65/1.00      | r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | sK4 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1099,plain,
% 1.65/1.00      ( v3_pre_topc(sK0(sK4,X0,X1),sK4)
% 1.65/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | v2_struct_0(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1098]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1103,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.65/1.00      | v3_pre_topc(sK0(sK4,X0,X1),sK4) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1099,c_30]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1104,plain,
% 1.65/1.00      ( v3_pre_topc(sK0(sK4,X0,X1),sK4)
% 1.65/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_1103]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2210,plain,
% 1.65/1.00      ( v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4)
% 1.65/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56))
% 1.65/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_1104]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2245,plain,
% 1.65/1.00      ( v3_pre_topc(sK0(sK4,X0_56,X1_56),sK4) = iProver_top
% 1.65/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2210]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3608,plain,
% 1.65/1.00      ( m1_connsp_2(sK0(sK4,X0_56,X1_56),sK4,X2_56) = iProver_top
% 1.65/1.00      | r2_hidden(X2_56,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.65/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_3402,c_2245]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_22,negated_conjecture,
% 1.65/1.00      ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
% 1.65/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2213,negated_conjecture,
% 1.65/1.00      ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2605,plain,
% 1.65/1.00      ( r2_hidden(sK5,k10_yellow_6(sK4,sK6)) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_16,plain,
% 1.65/1.00      ( ~ l1_waybel_0(X0,X1)
% 1.65/1.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | ~ v2_pre_topc(X1)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_796,plain,
% 1.65/1.00      ( ~ l1_waybel_0(X0,X1)
% 1.65/1.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | sK4 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_797,plain,
% 1.65/1.00      ( ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(sK4)
% 1.65/1.00      | ~ l1_pre_topc(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_796]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_801,plain,
% 1.65/1.00      ( ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_797,c_30,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_15,plain,
% 1.65/1.00      ( r1_waybel_0(X0,X1,X2)
% 1.65/1.00      | ~ m1_connsp_2(X2,X0,X3)
% 1.65/1.00      | ~ l1_waybel_0(X1,X0)
% 1.65/1.00      | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
% 1.65/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.65/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.65/1.00      | ~ v4_orders_2(X1)
% 1.65/1.00      | ~ v7_waybel_0(X1)
% 1.65/1.00      | ~ v2_pre_topc(X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_572,plain,
% 1.65/1.00      ( r1_waybel_0(X0,X1,X2)
% 1.65/1.00      | ~ m1_connsp_2(X2,X0,X3)
% 1.65/1.00      | ~ l1_waybel_0(X1,X0)
% 1.65/1.00      | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
% 1.65/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.65/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.65/1.00      | ~ v4_orders_2(X1)
% 1.65/1.00      | ~ v7_waybel_0(X1)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X0)
% 1.65/1.00      | sK4 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_573,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,X0,X1)
% 1.65/1.00      | ~ m1_connsp_2(X1,sK4,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(sK4)
% 1.65/1.00      | ~ l1_pre_topc(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_572]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_577,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,X0,X1)
% 1.65/1.00      | ~ m1_connsp_2(X1,sK4,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_573,c_30,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_601,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,X0,X1)
% 1.65/1.00      | ~ m1_connsp_2(X1,sK4,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
% 1.65/1.00      | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0) ),
% 1.65/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_577,c_0]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_819,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,X0,X1)
% 1.65/1.00      | ~ m1_connsp_2(X1,sK4,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0) ),
% 1.65/1.00      inference(backward_subsumption_resolution,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_801,c_601]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_24,negated_conjecture,
% 1.65/1.00      ( v7_waybel_0(sK6) ),
% 1.65/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1485,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,X0,X1)
% 1.65/1.00      | ~ m1_connsp_2(X1,sK4,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r2_hidden(X2,k10_yellow_6(sK4,X0))
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | sK6 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_819,c_24]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1486,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0)
% 1.65/1.00      | ~ m1_connsp_2(X0,sK4,X1)
% 1.65/1.00      | ~ l1_waybel_0(sK6,sK4)
% 1.65/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6))
% 1.65/1.00      | ~ v4_orders_2(sK6)
% 1.65/1.00      | v2_struct_0(sK6) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1485]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_26,negated_conjecture,
% 1.65/1.00      ( ~ v2_struct_0(sK6) ),
% 1.65/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_25,negated_conjecture,
% 1.65/1.00      ( v4_orders_2(sK6) ),
% 1.65/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_23,negated_conjecture,
% 1.65/1.00      ( l1_waybel_0(sK6,sK4) ),
% 1.65/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1490,plain,
% 1.65/1.00      ( ~ m1_connsp_2(X0,sK4,X1)
% 1.65/1.00      | r1_waybel_0(sK4,sK6,X0)
% 1.65/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6)) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1486,c_26,c_25,c_23]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1491,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0)
% 1.65/1.00      | ~ m1_connsp_2(X0,sK4,X1)
% 1.65/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK4,sK6)) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_1490]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2203,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0_56)
% 1.65/1.00      | ~ m1_connsp_2(X0_56,sK4,X1_56)
% 1.65/1.00      | ~ r2_hidden(X1_56,k10_yellow_6(sK4,sK6)) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_1491]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2615,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0_56) = iProver_top
% 1.65/1.00      | m1_connsp_2(X0_56,sK4,X1_56) != iProver_top
% 1.65/1.00      | r2_hidden(X1_56,k10_yellow_6(sK4,sK6)) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2203]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3034,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0_56) = iProver_top
% 1.65/1.00      | m1_connsp_2(X0_56,sK4,sK5) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_2605,c_2615]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3620,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56)) = iProver_top
% 1.65/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | r2_hidden(sK5,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_3608,c_3034]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1,plain,
% 1.65/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_17,plain,
% 1.65/1.00      ( ~ r1_waybel_0(X0,X1,X2)
% 1.65/1.00      | ~ r1_waybel_0(X0,X1,X3)
% 1.65/1.00      | ~ l1_waybel_0(X1,X0)
% 1.65/1.00      | ~ r1_xboole_0(X3,X2)
% 1.65/1.00      | ~ v4_orders_2(X1)
% 1.65/1.00      | ~ v7_waybel_0(X1)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_struct_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_349,plain,
% 1.65/1.00      ( ~ r1_waybel_0(X0,X1,X2)
% 1.65/1.00      | ~ r1_waybel_0(X0,X1,X3)
% 1.65/1.00      | ~ l1_waybel_0(X1,X0)
% 1.65/1.00      | ~ r1_xboole_0(X3,X2)
% 1.65/1.00      | ~ v4_orders_2(X1)
% 1.65/1.00      | ~ v7_waybel_0(X1)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X0) ),
% 1.65/1.00      inference(resolution,[status(thm)],[c_1,c_17]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1048,plain,
% 1.65/1.00      ( ~ r1_waybel_0(X0,X1,X2)
% 1.65/1.00      | ~ r1_waybel_0(X0,X1,X3)
% 1.65/1.00      | ~ l1_waybel_0(X1,X0)
% 1.65/1.00      | ~ r1_xboole_0(X3,X2)
% 1.65/1.00      | ~ v4_orders_2(X1)
% 1.65/1.00      | ~ v7_waybel_0(X1)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | sK4 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_349,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1049,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,X0,X1)
% 1.65/1.00      | ~ r1_waybel_0(sK4,X0,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r1_xboole_0(X1,X2)
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1048]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1053,plain,
% 1.65/1.00      ( v2_struct_0(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ r1_xboole_0(X1,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r1_waybel_0(sK4,X0,X2)
% 1.65/1.00      | ~ r1_waybel_0(sK4,X0,X1) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1049,c_30]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1054,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,X0,X1)
% 1.65/1.00      | ~ r1_waybel_0(sK4,X0,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r1_xboole_0(X1,X2)
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | ~ v7_waybel_0(X0)
% 1.65/1.00      | v2_struct_0(X0) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_1053]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1401,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,X0,X1)
% 1.65/1.00      | ~ r1_waybel_0(sK4,X0,X2)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | ~ r1_xboole_0(X1,X2)
% 1.65/1.00      | ~ v4_orders_2(X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | sK6 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_1054,c_24]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1402,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,sK6,X0)
% 1.65/1.00      | ~ r1_waybel_0(sK4,sK6,X1)
% 1.65/1.00      | ~ l1_waybel_0(sK6,sK4)
% 1.65/1.00      | ~ r1_xboole_0(X1,X0)
% 1.65/1.00      | ~ v4_orders_2(sK6)
% 1.65/1.00      | v2_struct_0(sK6) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1401]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1406,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,sK6,X1)
% 1.65/1.00      | ~ r1_waybel_0(sK4,sK6,X0)
% 1.65/1.00      | ~ r1_xboole_0(X1,X0) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1402,c_26,c_25,c_23]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1407,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,sK6,X0)
% 1.65/1.00      | ~ r1_waybel_0(sK4,sK6,X1)
% 1.65/1.00      | ~ r1_xboole_0(X0,X1) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_1406]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2,plain,
% 1.65/1.00      ( r1_xboole_0(X0,sK0(X1,X0,X2))
% 1.65/1.00      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1201,plain,
% 1.65/1.00      ( r1_xboole_0(X0,sK0(X1,X0,X2))
% 1.65/1.00      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | sK4 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1202,plain,
% 1.65/1.00      ( r1_xboole_0(X0,sK0(sK4,X0,X1))
% 1.65/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | v2_struct_0(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1201]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1206,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.65/1.00      | r1_xboole_0(X0,sK0(sK4,X0,X1)) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1202,c_30]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1207,plain,
% 1.65/1.00      ( r1_xboole_0(X0,sK0(sK4,X0,X1))
% 1.65/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_1206]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1643,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,sK6,X0)
% 1.65/1.00      | ~ r1_waybel_0(sK4,sK6,X1)
% 1.65/1.00      | r2_hidden(X2,k2_pre_topc(sK4,X3))
% 1.65/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.65/1.00      | X3 != X1
% 1.65/1.00      | sK0(sK4,X3,X2) != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_1407,c_1207]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1644,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,sK6,X0)
% 1.65/1.00      | ~ r1_waybel_0(sK4,sK6,sK0(sK4,X0,X1))
% 1.65/1.00      | r2_hidden(X1,k2_pre_topc(sK4,X0))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1643]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2197,plain,
% 1.65/1.00      ( ~ r1_waybel_0(sK4,sK6,X0_56)
% 1.65/1.00      | ~ r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56))
% 1.65/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56))
% 1.65/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
% 1.65/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_1644]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2621,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
% 1.65/1.00      | r1_waybel_0(sK4,sK6,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.65/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2197]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3659,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
% 1.65/1.00      | r2_hidden(X1_56,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | r2_hidden(sK5,sK0(sK4,X0_56,X1_56)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_3620,c_2621]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3999,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
% 1.65/1.00      | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.65/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_2610,c_3659]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_27,negated_conjecture,
% 1.65/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.65/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_34,plain,
% 1.65/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_4004,plain,
% 1.65/1.00      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.65/1.00      | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | r1_waybel_0(sK4,sK6,X0_56) != iProver_top ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_3999,c_34]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_4005,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,X0_56) != iProver_top
% 1.65/1.00      | r2_hidden(sK5,k2_pre_topc(sK4,X0_56)) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_4004]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_4013,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,sK7) != iProver_top
% 1.65/1.00      | r2_hidden(sK5,k2_pre_topc(sK4,sK7)) = iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_2604,c_4005]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_18,plain,
% 1.65/1.00      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
% 1.65/1.00      | ~ l1_waybel_0(X1,X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_struct_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_329,plain,
% 1.65/1.00      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
% 1.65/1.00      | ~ l1_waybel_0(X1,X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ l1_pre_topc(X0) ),
% 1.65/1.00      inference(resolution,[status(thm)],[c_1,c_18]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1079,plain,
% 1.65/1.00      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
% 1.65/1.00      | ~ l1_waybel_0(X1,X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | sK4 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_329,c_28]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1080,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,X0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),u1_waybel_0(sK4,X0)))
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | v2_struct_0(sK4) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1079]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1084,plain,
% 1.65/1.00      ( v2_struct_0(X0)
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | r1_waybel_0(sK4,X0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),u1_waybel_0(sK4,X0))) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1080,c_30]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1085,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,X0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),u1_waybel_0(sK4,X0)))
% 1.65/1.00      | ~ l1_waybel_0(X0,sK4)
% 1.65/1.00      | v2_struct_0(X0) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_1084]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1630,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,X0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),u1_waybel_0(sK4,X0)))
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | sK6 != X0
% 1.65/1.00      | sK4 != sK4 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_1085]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1631,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)))
% 1.65/1.00      | v2_struct_0(sK6) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_1630]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1633,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_1631,c_26]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2198,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_1633]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2620,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6))) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2198]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_20,negated_conjecture,
% 1.65/1.00      ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
% 1.65/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2215,negated_conjecture,
% 1.65/1.00      ( k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK4),u1_waybel_0(sK4,sK6)) = sK7 ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2634,plain,
% 1.65/1.00      ( r1_waybel_0(sK4,sK6,sK7) = iProver_top ),
% 1.65/1.00      inference(light_normalisation,[status(thm)],[c_2620,c_2215]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_19,negated_conjecture,
% 1.65/1.00      ( ~ r2_hidden(sK5,k2_pre_topc(sK4,sK7)) ),
% 1.65/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_41,plain,
% 1.65/1.00      ( r2_hidden(sK5,k2_pre_topc(sK4,sK7)) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(contradiction,plain,
% 1.65/1.00      ( $false ),
% 1.65/1.00      inference(minisat,[status(thm)],[c_4013,c_2634,c_41]) ).
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  ------                               Statistics
% 1.65/1.00  
% 1.65/1.00  ------ General
% 1.65/1.00  
% 1.65/1.00  abstr_ref_over_cycles:                  0
% 1.65/1.00  abstr_ref_under_cycles:                 0
% 1.65/1.00  gc_basic_clause_elim:                   0
% 1.65/1.00  forced_gc_time:                         0
% 1.65/1.00  parsing_time:                           0.009
% 1.65/1.00  unif_index_cands_time:                  0.
% 1.65/1.00  unif_index_add_time:                    0.
% 1.65/1.00  orderings_time:                         0.
% 1.65/1.00  out_proof_time:                         0.014
% 1.65/1.00  total_time:                             0.18
% 1.65/1.00  num_of_symbols:                         59
% 1.65/1.00  num_of_terms:                           3398
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing
% 1.65/1.00  
% 1.65/1.00  num_of_splits:                          0
% 1.65/1.00  num_of_split_atoms:                     0
% 1.65/1.00  num_of_reused_defs:                     0
% 1.65/1.00  num_eq_ax_congr_red:                    50
% 1.65/1.00  num_of_sem_filtered_clauses:            1
% 1.65/1.00  num_of_subtypes:                        4
% 1.65/1.00  monotx_restored_types:                  1
% 1.65/1.00  sat_num_of_epr_types:                   0
% 1.65/1.00  sat_num_of_non_cyclic_types:            0
% 1.65/1.00  sat_guarded_non_collapsed_types:        0
% 1.65/1.00  num_pure_diseq_elim:                    0
% 1.65/1.00  simp_replaced_by:                       0
% 1.65/1.00  res_preprocessed:                       111
% 1.65/1.00  prep_upred:                             0
% 1.65/1.00  prep_unflattend:                        69
% 1.65/1.00  smt_new_axioms:                         0
% 1.65/1.00  pred_elim_cands:                        5
% 1.65/1.00  pred_elim:                              8
% 1.65/1.00  pred_elim_cl:                           10
% 1.65/1.00  pred_elim_cycles:                       17
% 1.65/1.00  merged_defs:                            0
% 1.65/1.00  merged_defs_ncl:                        0
% 1.65/1.00  bin_hyper_res:                          0
% 1.65/1.00  prep_cycles:                            4
% 1.65/1.00  pred_elim_time:                         0.04
% 1.65/1.00  splitting_time:                         0.
% 1.65/1.00  sem_filter_time:                        0.
% 1.65/1.00  monotx_time:                            0.001
% 1.65/1.00  subtype_inf_time:                       0.002
% 1.65/1.00  
% 1.65/1.00  ------ Problem properties
% 1.65/1.00  
% 1.65/1.00  clauses:                                21
% 1.65/1.00  conjectures:                            5
% 1.65/1.00  epr:                                    0
% 1.65/1.00  horn:                                   14
% 1.65/1.00  ground:                                 7
% 1.65/1.00  unary:                                  7
% 1.65/1.00  binary:                                 0
% 1.65/1.00  lits:                                   61
% 1.65/1.00  lits_eq:                                5
% 1.65/1.00  fd_pure:                                0
% 1.65/1.00  fd_pseudo:                              0
% 1.65/1.00  fd_cond:                                4
% 1.65/1.00  fd_pseudo_cond:                         0
% 1.65/1.00  ac_symbols:                             0
% 1.65/1.00  
% 1.65/1.00  ------ Propositional Solver
% 1.65/1.00  
% 1.65/1.00  prop_solver_calls:                      27
% 1.65/1.00  prop_fast_solver_calls:                 1522
% 1.65/1.00  smt_solver_calls:                       0
% 1.65/1.00  smt_fast_solver_calls:                  0
% 1.65/1.00  prop_num_of_clauses:                    998
% 1.65/1.00  prop_preprocess_simplified:             3872
% 1.65/1.00  prop_fo_subsumed:                       75
% 1.65/1.00  prop_solver_time:                       0.
% 1.65/1.00  smt_solver_time:                        0.
% 1.65/1.00  smt_fast_solver_time:                   0.
% 1.65/1.00  prop_fast_solver_time:                  0.
% 1.65/1.00  prop_unsat_core_time:                   0.
% 1.65/1.00  
% 1.65/1.00  ------ QBF
% 1.65/1.00  
% 1.65/1.00  qbf_q_res:                              0
% 1.65/1.00  qbf_num_tautologies:                    0
% 1.65/1.00  qbf_prep_cycles:                        0
% 1.65/1.00  
% 1.65/1.00  ------ BMC1
% 1.65/1.00  
% 1.65/1.00  bmc1_current_bound:                     -1
% 1.65/1.00  bmc1_last_solved_bound:                 -1
% 1.65/1.00  bmc1_unsat_core_size:                   -1
% 1.65/1.00  bmc1_unsat_core_parents_size:           -1
% 1.65/1.00  bmc1_merge_next_fun:                    0
% 1.65/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation
% 1.65/1.00  
% 1.65/1.00  inst_num_of_clauses:                    187
% 1.65/1.00  inst_num_in_passive:                    11
% 1.65/1.00  inst_num_in_active:                     158
% 1.65/1.00  inst_num_in_unprocessed:                18
% 1.65/1.00  inst_num_of_loops:                      180
% 1.65/1.00  inst_num_of_learning_restarts:          0
% 1.65/1.00  inst_num_moves_active_passive:          17
% 1.65/1.00  inst_lit_activity:                      0
% 1.65/1.00  inst_lit_activity_moves:                0
% 1.65/1.00  inst_num_tautologies:                   0
% 1.65/1.00  inst_num_prop_implied:                  0
% 1.65/1.00  inst_num_existing_simplified:           0
% 1.65/1.00  inst_num_eq_res_simplified:             0
% 1.65/1.00  inst_num_child_elim:                    0
% 1.65/1.00  inst_num_of_dismatching_blockings:      19
% 1.65/1.00  inst_num_of_non_proper_insts:           184
% 1.65/1.00  inst_num_of_duplicates:                 0
% 1.65/1.00  inst_inst_num_from_inst_to_res:         0
% 1.65/1.00  inst_dismatching_checking_time:         0.
% 1.65/1.00  
% 1.65/1.00  ------ Resolution
% 1.65/1.00  
% 1.65/1.00  res_num_of_clauses:                     0
% 1.65/1.00  res_num_in_passive:                     0
% 1.65/1.00  res_num_in_active:                      0
% 1.65/1.00  res_num_of_loops:                       115
% 1.65/1.00  res_forward_subset_subsumed:            32
% 1.65/1.00  res_backward_subset_subsumed:           2
% 1.65/1.00  res_forward_subsumed:                   0
% 1.65/1.00  res_backward_subsumed:                  0
% 1.65/1.00  res_forward_subsumption_resolution:     11
% 1.65/1.00  res_backward_subsumption_resolution:    3
% 1.65/1.00  res_clause_to_clause_subsumption:       215
% 1.65/1.00  res_orphan_elimination:                 0
% 1.65/1.00  res_tautology_del:                      24
% 1.65/1.00  res_num_eq_res_simplified:              0
% 1.65/1.00  res_num_sel_changes:                    0
% 1.65/1.00  res_moves_from_active_to_pass:          0
% 1.65/1.00  
% 1.65/1.00  ------ Superposition
% 1.65/1.00  
% 1.65/1.00  sup_time_total:                         0.
% 1.65/1.00  sup_time_generating:                    0.
% 1.65/1.00  sup_time_sim_full:                      0.
% 1.65/1.00  sup_time_sim_immed:                     0.
% 1.65/1.00  
% 1.65/1.00  sup_num_of_clauses:                     43
% 1.65/1.00  sup_num_in_active:                      36
% 1.65/1.00  sup_num_in_passive:                     7
% 1.65/1.00  sup_num_of_loops:                       35
% 1.65/1.00  sup_fw_superposition:                   19
% 1.65/1.00  sup_bw_superposition:                   19
% 1.65/1.00  sup_immediate_simplified:               6
% 1.65/1.00  sup_given_eliminated:                   0
% 1.65/1.00  comparisons_done:                       0
% 1.65/1.00  comparisons_avoided:                    0
% 1.65/1.00  
% 1.65/1.00  ------ Simplifications
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  sim_fw_subset_subsumed:                 4
% 1.65/1.00  sim_bw_subset_subsumed:                 0
% 1.65/1.00  sim_fw_subsumed:                        1
% 1.65/1.00  sim_bw_subsumed:                        1
% 1.65/1.00  sim_fw_subsumption_res:                 2
% 1.65/1.00  sim_bw_subsumption_res:                 0
% 1.65/1.00  sim_tautology_del:                      3
% 1.65/1.00  sim_eq_tautology_del:                   5
% 1.65/1.00  sim_eq_res_simp:                        0
% 1.65/1.00  sim_fw_demodulated:                     0
% 1.65/1.00  sim_bw_demodulated:                     0
% 1.65/1.00  sim_light_normalised:                   1
% 1.65/1.00  sim_joinable_taut:                      0
% 1.65/1.00  sim_joinable_simp:                      0
% 1.65/1.00  sim_ac_normalised:                      0
% 1.65/1.00  sim_smt_subsumption:                    0
% 1.65/1.00  
%------------------------------------------------------------------------------
