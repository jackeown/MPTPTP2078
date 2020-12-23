%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 (24469 expanded)
%              Number of leaves         :   19 (11372 expanded)
%              Depth                    :   18
%              Number of atoms          :  736 (272296 expanded)
%              Number of equality atoms :   18 ( 892 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f590,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f59,f562,f225,f224,f223,f245,f222,f158,f230,f87])).

fof(f87,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_waybel_0(X0,X1,X8)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
                        & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2)) )
                      | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
                      | r2_hidden(sK4(X0,X1,X2),X2) )
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
                            & m1_connsp_2(sK6(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f49,f48,f47])).

fof(f47,plain,(
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
              & m1_connsp_2(X4,X0,sK4(X0,X1,X2)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK4(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
        & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
        & m1_connsp_2(sK6(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f230,plain,(
    m1_subset_1(k10_yellow_6(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f225,f224,f223,f222,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f158,plain,(
    r2_hidden(sK2,k10_yellow_6(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))))) ),
    inference(unit_resulting_resolution,[],[f151,f62])).

fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(sK2,k10_yellow_6(sK0,sK3(X3)))
      | ~ m2_yellow_6(X3,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ! [X3] :
        ( ( r2_hidden(sK2,k10_yellow_6(sK0,sK3(X3)))
          & m2_yellow_6(sK3(X3),sK0,X3) )
        | ~ m2_yellow_6(X3,sK0,sK1) )
    & ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(X2,k10_yellow_6(X0,X4))
                        & m2_yellow_6(X4,X0,X3) )
                    | ~ m2_yellow_6(X3,X0,X1) )
                & ~ r2_hidden(X2,k10_yellow_6(X0,X1))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(X2,k10_yellow_6(sK0,X4))
                      & m2_yellow_6(X4,sK0,X3) )
                  | ~ m2_yellow_6(X3,sK0,X1) )
              & ~ r2_hidden(X2,k10_yellow_6(sK0,X1))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r2_hidden(X2,k10_yellow_6(sK0,X4))
                    & m2_yellow_6(X4,sK0,X3) )
                | ~ m2_yellow_6(X3,sK0,X1) )
            & ~ r2_hidden(X2,k10_yellow_6(sK0,X1))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X2,k10_yellow_6(sK0,X4))
                  & m2_yellow_6(X4,sK0,X3) )
              | ~ m2_yellow_6(X3,sK0,sK1) )
          & ~ r2_hidden(X2,k10_yellow_6(sK0,sK1))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( r2_hidden(X2,k10_yellow_6(sK0,X4))
                & m2_yellow_6(X4,sK0,X3) )
            | ~ m2_yellow_6(X3,sK0,sK1) )
        & ~ r2_hidden(X2,k10_yellow_6(sK0,sK1))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ! [X3] :
          ( ? [X4] :
              ( r2_hidden(sK2,k10_yellow_6(sK0,X4))
              & m2_yellow_6(X4,sK0,X3) )
          | ~ m2_yellow_6(X3,sK0,sK1) )
      & ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X3] :
      ( ? [X4] :
          ( r2_hidden(sK2,k10_yellow_6(sK0,X4))
          & m2_yellow_6(X4,sK0,X3) )
     => ( r2_hidden(sK2,k10_yellow_6(sK0,sK3(X3)))
        & m2_yellow_6(sK3(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X4))
                      & m2_yellow_6(X4,X0,X3) )
                  | ~ m2_yellow_6(X3,X0,X1) )
              & ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X4))
                      & m2_yellow_6(X4,X0,X3) )
                  | ~ m2_yellow_6(X3,X0,X1) )
              & ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m2_yellow_6(X3,X0,X1)
                       => ? [X4] :
                            ( r2_hidden(X2,k10_yellow_6(X0,X4))
                            & m2_yellow_6(X4,X0,X3) ) )
                    & ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ? [X4] :
                          ( r2_hidden(X2,k10_yellow_6(X0,X4))
                          & m2_yellow_6(X4,X0,X3) ) )
                  & ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_6)).

fof(f151,plain,(
    m2_yellow_6(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f148,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
              | ~ r2_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
              | ~ r2_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
             => m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_6)).

fof(f148,plain,(
    r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f55,f58,f147,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

fof(f147,plain,(
    ~ r1_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f56,f57,f58,f59,f60,f145,f85])).

fof(f85,plain,(
    ! [X6,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
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
    inference(cnf_transformation,[],[f50])).

fof(f145,plain,(
    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f56,f57,f58,f79])).

fof(f60,plain,(
    ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f121,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f222,plain,(
    l1_waybel_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK0) ),
    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f159,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | l1_waybel_0(X2,X0)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f159,plain,(
    m2_yellow_6(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f151,f61])).

fof(f61,plain,(
    ! [X3] :
      ( m2_yellow_6(sK3(X3),sK0,X3)
      | ~ m2_yellow_6(X3,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f160,plain,(
    l1_waybel_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f151,f83])).

fof(f152,plain,(
    v7_waybel_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f148,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | v7_waybel_0(k5_yellow_6(X0,X1,X2))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v7_waybel_0(k5_yellow_6(X0,X1,X2))
                & ~ v2_struct_0(k5_yellow_6(X0,X1,X2)) )
              | ~ r2_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v7_waybel_0(k5_yellow_6(X0,X1,X2))
                & ~ v2_struct_0(k5_yellow_6(X0,X1,X2)) )
              | ~ r2_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
             => ( v7_waybel_0(k5_yellow_6(X0,X1,X2))
                & ~ v2_struct_0(k5_yellow_6(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_6)).

fof(f134,plain,(
    ! [X0] : v4_orders_2(k5_yellow_6(sK0,sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f121,f56,f58,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k5_yellow_6(X0,X1,X2))
      | ~ l1_waybel_0(X1,X0)
      | ~ v4_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_orders_2(k5_yellow_6(X0,X1,X2))
      | ~ l1_waybel_0(X1,X0)
      | ~ v4_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_orders_2(k5_yellow_6(X0,X1,X2))
      | ~ l1_waybel_0(X1,X0)
      | ~ v4_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X1,X0)
        & v4_orders_2(X1)
        & l1_struct_0(X0) )
     => v4_orders_2(k5_yellow_6(X0,X1,X2)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X1,X0)
        & v4_orders_2(X1)
        & l1_struct_0(X0) )
     => ( v6_waybel_0(k5_yellow_6(X0,X1,X2),X0)
        & v4_orders_2(k5_yellow_6(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X1,X0)
        & v4_orders_2(X1)
        & l1_struct_0(X0) )
     => ( v2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_yellow_6(X0,X1,X2),X0)
        & v4_orders_2(k5_yellow_6(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_yellow_6)).

fof(f153,plain,(
    ~ v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f148,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k5_yellow_6(X0,X1,X2))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f245,plain,(
    ~ r1_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f52,f121,f225,f222,f242,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f242,plain,(
    r2_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f225,f224,f223,f222,f239,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,X2)
      | r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

fof(f239,plain,(
    r1_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f225,f222,f221,f78])).

fof(f221,plain,(
    ~ r2_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),k6_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f187,f159,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_waybel_0(X0,X2,X3)
      | r2_waybel_0(X0,X1,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

% (17022)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (17011)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (17012)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (17019)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (17018)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (17030)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (17021)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (17028)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).

fof(f187,plain,(
    ~ r2_waybel_0(sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),k6_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f153,f160,f157,f77])).

fof(f157,plain,(
    r1_waybel_0(sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f151,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,k5_yellow_6(X0,X1,X2),X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X3,X2)
      | k5_yellow_6(X0,X1,X2) != X3
      | ~ m2_yellow_6(X3,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( r1_waybel_0(X0,X3,X2)
              | k5_yellow_6(X0,X1,X2) != X3
              | ~ m2_yellow_6(X3,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( r1_waybel_0(X0,X3,X2)
              | k5_yellow_6(X0,X1,X2) != X3
              | ~ m2_yellow_6(X3,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( m2_yellow_6(X3,X0,X1)
             => ( k5_yellow_6(X0,X1,X2) = X3
               => r1_waybel_0(X0,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_yellow_6)).

fof(f223,plain,(
    v7_waybel_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f159,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v7_waybel_0(X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f224,plain,(
    v4_orders_2(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f159,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v4_orders_2(X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f225,plain,(
    ~ v2_struct_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))) ),
    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f159,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f562,plain,(
    m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f56,f57,f58,f59,f60,f145,f86])).

fof(f86,plain,(
    ! [X6,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | m1_connsp_2(sK6(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK6(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f50])).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (17014)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (17020)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (17024)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (17023)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (17016)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (17029)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (17031)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (17017)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (17020)Refutation not found, incomplete strategy% (17020)------------------------------
% 0.20/0.49  % (17020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17020)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17020)Memory used [KB]: 6140
% 0.20/0.49  % (17020)Time elapsed: 0.075 s
% 0.20/0.49  % (17020)------------------------------
% 0.20/0.49  % (17020)------------------------------
% 0.20/0.49  % (17023)Refutation not found, incomplete strategy% (17023)------------------------------
% 0.20/0.49  % (17023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17023)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17023)Memory used [KB]: 1791
% 0.20/0.49  % (17023)Time elapsed: 0.083 s
% 0.20/0.49  % (17023)------------------------------
% 0.20/0.49  % (17023)------------------------------
% 0.20/0.49  % (17009)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (17009)Refutation not found, incomplete strategy% (17009)------------------------------
% 0.20/0.49  % (17009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17009)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17009)Memory used [KB]: 6140
% 0.20/0.49  % (17009)Time elapsed: 0.089 s
% 0.20/0.49  % (17009)------------------------------
% 0.20/0.49  % (17009)------------------------------
% 0.20/0.49  % (17010)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (17013)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (17024)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f590,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f53,f54,f59,f562,f225,f224,f223,f245,f222,f158,f230,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X6,X0,X8,X1] : (~v2_pre_topc(X0) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_waybel_0(X0,X1,X8) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X6,X2,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK5(X0,X1,X2)) & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK4(X0,X1,X2))) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) & m1_connsp_2(sK6(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f49,f48,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK4(X0,X1,X2))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK4(X0,X1,X2))) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK4(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK5(X0,X1,X2)) & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) & m1_connsp_2(sK6(X0,X1,X6),X0,X6)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(rectify,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    m1_subset_1(k10_yellow_6(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f53,f54,f225,f224,f223,f222,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    r2_hidden(sK2,k10_yellow_6(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f151,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X3] : (r2_hidden(sK2,k10_yellow_6(sK0,sK3(X3))) | ~m2_yellow_6(X3,sK0,sK1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ((! [X3] : ((r2_hidden(sK2,k10_yellow_6(sK0,sK3(X3))) & m2_yellow_6(sK3(X3),sK0,X3)) | ~m2_yellow_6(X3,sK0,sK1)) & ~r2_hidden(sK2,k10_yellow_6(sK0,sK1)) & m1_subset_1(sK2,u1_struct_0(sK0))) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f42,f41,f40,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & m2_yellow_6(X4,X0,X3)) | ~m2_yellow_6(X3,X0,X1)) & ~r2_hidden(X2,k10_yellow_6(X0,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (? [X4] : (r2_hidden(X2,k10_yellow_6(sK0,X4)) & m2_yellow_6(X4,sK0,X3)) | ~m2_yellow_6(X3,sK0,X1)) & ~r2_hidden(X2,k10_yellow_6(sK0,X1)) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (! [X3] : (? [X4] : (r2_hidden(X2,k10_yellow_6(sK0,X4)) & m2_yellow_6(X4,sK0,X3)) | ~m2_yellow_6(X3,sK0,X1)) & ~r2_hidden(X2,k10_yellow_6(sK0,X1)) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (! [X3] : (? [X4] : (r2_hidden(X2,k10_yellow_6(sK0,X4)) & m2_yellow_6(X4,sK0,X3)) | ~m2_yellow_6(X3,sK0,sK1)) & ~r2_hidden(X2,k10_yellow_6(sK0,sK1)) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ? [X2] : (! [X3] : (? [X4] : (r2_hidden(X2,k10_yellow_6(sK0,X4)) & m2_yellow_6(X4,sK0,X3)) | ~m2_yellow_6(X3,sK0,sK1)) & ~r2_hidden(X2,k10_yellow_6(sK0,sK1)) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (? [X4] : (r2_hidden(sK2,k10_yellow_6(sK0,X4)) & m2_yellow_6(X4,sK0,X3)) | ~m2_yellow_6(X3,sK0,sK1)) & ~r2_hidden(sK2,k10_yellow_6(sK0,sK1)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X3] : (? [X4] : (r2_hidden(sK2,k10_yellow_6(sK0,X4)) & m2_yellow_6(X4,sK0,X3)) => (r2_hidden(sK2,k10_yellow_6(sK0,sK3(X3))) & m2_yellow_6(sK3(X3),sK0,X3)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & m2_yellow_6(X4,X0,X3)) | ~m2_yellow_6(X3,X0,X1)) & ~r2_hidden(X2,k10_yellow_6(X0,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & m2_yellow_6(X4,X0,X3)) | ~m2_yellow_6(X3,X0,X1)) & ~r2_hidden(X2,k10_yellow_6(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & m2_yellow_6(X4,X0,X3))) & ~r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & m2_yellow_6(X4,X0,X3))) & ~r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_6)).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    m2_yellow_6(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK0,sK1)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f148,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1) | ~r2_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1) | ~r2_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) => m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_6)).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f55,f58,f147,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r1_waybel_0(X0,X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ~r1_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f56,f57,f58,f59,f60,f145,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X6,X0,X1] : (~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f50])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f56,f57,f58,f79])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~r2_hidden(sK2,k10_yellow_6(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    l1_waybel_0(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    v7_waybel_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    v4_orders_2(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f54,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    l1_waybel_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK0)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f159,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | l1_waybel_0(X2,X0) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    m2_yellow_6(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f151,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X3] : (m2_yellow_6(sK3(X3),sK0,X3) | ~m2_yellow_6(X3,sK0,sK1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    l1_waybel_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK0)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f151,f83])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    v7_waybel_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f148,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_waybel_0(X0,X1,X2) | v7_waybel_0(k5_yellow_6(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((v7_waybel_0(k5_yellow_6(X0,X1,X2)) & ~v2_struct_0(k5_yellow_6(X0,X1,X2))) | ~r2_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((v7_waybel_0(k5_yellow_6(X0,X1,X2)) & ~v2_struct_0(k5_yellow_6(X0,X1,X2))) | ~r2_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) => (v7_waybel_0(k5_yellow_6(X0,X1,X2)) & ~v2_struct_0(k5_yellow_6(X0,X1,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_6)).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ( ! [X0] : (v4_orders_2(k5_yellow_6(sK0,sK1,X0))) )),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f121,f56,f58,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v4_orders_2(k5_yellow_6(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v4_orders_2(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v4_orders_2(k5_yellow_6(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v4_orders_2(X1) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v4_orders_2(k5_yellow_6(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v4_orders_2(X1) | ~l1_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & l1_struct_0(X0)) => v4_orders_2(k5_yellow_6(X0,X1,X2)))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & l1_struct_0(X0)) => (v6_waybel_0(k5_yellow_6(X0,X1,X2),X0) & v4_orders_2(k5_yellow_6(X0,X1,X2))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & l1_struct_0(X0)) => (v2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1) & v6_waybel_0(k5_yellow_6(X0,X1,X2),X0) & v4_orders_2(k5_yellow_6(X0,X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_yellow_6)).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ~v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f148,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_struct_0(k5_yellow_6(X0,X1,X2)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    ~r1_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK6(sK0,sK1,sK2))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f225,f222,f242,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f51])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    r2_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f225,f224,f223,f222,f239,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    r1_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f225,f222,f221,f78])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ~r2_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),k6_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f187,f159,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_waybel_0(X0,X2,X3) | r2_waybel_0(X0,X1,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  % (17022)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (17011)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (17012)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (17019)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (17018)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (17030)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (17021)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (17028)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    ~r2_waybel_0(sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),k6_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f52,f121,f153,f160,f157,f77])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    r1_waybel_0(sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f52,f121,f55,f56,f57,f58,f151,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1) | ~l1_waybel_0(X1,X0) | r1_waybel_0(X0,k5_yellow_6(X0,X1,X2),X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X3,X2) | k5_yellow_6(X0,X1,X2) != X3 | ~m2_yellow_6(X3,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2,X3] : (r1_waybel_0(X0,X3,X2) | k5_yellow_6(X0,X1,X2) != X3 | ~m2_yellow_6(X3,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2,X3] : ((r1_waybel_0(X0,X3,X2) | k5_yellow_6(X0,X1,X2) != X3) | ~m2_yellow_6(X3,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : (m2_yellow_6(X3,X0,X1) => (k5_yellow_6(X0,X1,X2) = X3 => r1_waybel_0(X0,X3,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_yellow_6)).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    v7_waybel_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f159,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | v7_waybel_0(X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    v4_orders_2(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f159,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | v4_orders_2(X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    ~v2_struct_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f52,f121,f153,f134,f152,f160,f159,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f562,plain,(
% 0.20/0.52    m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f56,f57,f58,f59,f60,f145,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X6,X0,X1] : (~v2_pre_topc(X0) | m1_connsp_2(sK6(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r2_hidden(X6,k10_yellow_6(X0,X1)) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK6(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (17024)------------------------------
% 0.20/0.52  % (17024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17024)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (17024)Memory used [KB]: 11385
% 0.20/0.52  % (17024)Time elapsed: 0.036 s
% 0.20/0.52  % (17024)------------------------------
% 0.20/0.52  % (17024)------------------------------
% 0.20/0.52  % (17005)Success in time 0.163 s
%------------------------------------------------------------------------------
