%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1948+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:57 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  145 (20992 expanded)
%              Number of leaves         :   20 (9668 expanded)
%              Depth                    :   20
%              Number of atoms          :  869 (231180 expanded)
%              Number of equality atoms :   18 ( 688 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f746,plain,(
    $false ),
    inference(subsumption_resolution,[],[f740,f700])).

fof(f700,plain,(
    ~ r1_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f55,f93,f508,f519,f530,f561,f649,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
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
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

fof(f649,plain,(
    ~ r2_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f55,f93,f229,f230,f231,f420,f157,f225,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).

% (2735)Refutation not found, incomplete strategy% (2735)------------------------------
% (2735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2735)Termination reason: Refutation not found, incomplete strategy

% (2735)Memory used [KB]: 6140
% (2735)Time elapsed: 0.090 s
% (2735)------------------------------
% (2735)------------------------------
fof(f225,plain,(
    m2_yellow_6(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f184,f64])).

fof(f64,plain,(
    ! [X3] :
      ( ~ m2_yellow_6(X3,sK0,sK1)
      | m2_yellow_6(sK3(X3),sK0,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f44,f43,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f184,plain,(
    m2_yellow_6(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f55,f93,f58,f59,f60,f61,f163,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
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

fof(f163,plain,(
    r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f55,f93,f58,f61,f132,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f132,plain,(
    ~ r1_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f58,f59,f60,f61,f62,f63,f129,f89])).

fof(f89,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f48,f51,f50,f49])).

fof(f49,plain,(
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

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK4(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
        & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
        & m1_connsp_2(sK6(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

% (2746)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (2752)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (2747)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (2739)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (2745)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (2736)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (2755)Refutation not found, incomplete strategy% (2755)------------------------------
% (2755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2755)Termination reason: Refutation not found, incomplete strategy

% (2755)Memory used [KB]: 10618
% (2755)Time elapsed: 0.105 s
% (2755)------------------------------
% (2755)------------------------------
fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f129,plain,(
    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f58,f59,f60,f61,f82])).

fof(f82,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f63,plain,(
    ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f157,plain,(
    ! [X0] : l1_waybel_0(k5_yellow_6(sK0,sK1,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f93,f61,f130,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f130,plain,(
    ! [X0] : m1_yellow_6(k5_yellow_6(sK0,sK1,X0),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f93,f61,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_yellow_6(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_yellow_6)).

fof(f420,plain,(
    ~ r2_waybel_0(sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f55,f93,f229,f157,f220,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
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
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f220,plain,(
    r1_waybel_0(sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))),k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f55,f93,f58,f59,f60,f61,f184,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m2_yellow_6(k5_yellow_6(X0,X1,X2),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r1_waybel_0(X0,k5_yellow_6(X0,X1,X2),X2)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f231,plain,(
    v7_waybel_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f55,f93,f58,f59,f60,f61,f184,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | v7_waybel_0(X2)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f230,plain,(
    v4_orders_2(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f55,f93,f58,f59,f60,f61,f184,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | v4_orders_2(X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f229,plain,(
    ~ v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f55,f93,f58,f59,f60,f61,f184,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v2_struct_0(X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f561,plain,(
    l1_waybel_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK0) ),
    inference(subsumption_resolution,[],[f560,f163])).

fof(f560,plain,
    ( l1_waybel_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK0)
    | ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(resolution,[],[f486,f341])).

fof(f341,plain,(
    ! [X4] :
      ( m2_yellow_6(sK3(k5_yellow_6(sK0,sK1,X4)),sK0,k5_yellow_6(sK0,sK1,X4))
      | ~ r2_waybel_0(sK0,sK1,X4) ) ),
    inference(resolution,[],[f334,f64])).

fof(f334,plain,(
    ! [X0] :
      ( m2_yellow_6(k5_yellow_6(sK0,sK1,X0),sK0,sK1)
      | ~ r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f333,f58])).

fof(f333,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK1,X0)
      | v2_struct_0(sK1)
      | m2_yellow_6(k5_yellow_6(sK0,sK1,X0),sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f332,f59])).

fof(f332,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK1,X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | m2_yellow_6(k5_yellow_6(sK0,sK1,X0),sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f329,f60])).

fof(f329,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK1,X0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | m2_yellow_6(k5_yellow_6(sK0,sK1,X0),sK0,sK1) ) ),
    inference(resolution,[],[f118,f61])).

fof(f118,plain,(
    ! [X2,X3] :
      ( ~ l1_waybel_0(X2,sK0)
      | ~ r2_waybel_0(sK0,X2,X3)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | m2_yellow_6(k5_yellow_6(sK0,X2,X3),sK0,X2) ) ),
    inference(subsumption_resolution,[],[f104,f55])).

% (2745)Refutation not found, incomplete strategy% (2745)------------------------------
% (2745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2745)Termination reason: Refutation not found, incomplete strategy

% (2745)Memory used [KB]: 6268
% (2745)Time elapsed: 0.109 s
% (2745)------------------------------
% (2745)------------------------------
fof(f104,plain,(
    ! [X2,X3] :
      ( ~ r2_waybel_0(sK0,X2,X3)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | m2_yellow_6(k5_yellow_6(sK0,X2,X3),sK0,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f75])).

fof(f486,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | l1_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f485,f229])).

fof(f485,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | l1_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f482,f230])).

fof(f482,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | ~ v4_orders_2(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | l1_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f272,f231])).

% (2736)Refutation not found, incomplete strategy% (2736)------------------------------
% (2736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2736)Termination reason: Refutation not found, incomplete strategy

% (2736)Memory used [KB]: 10618
% (2736)Time elapsed: 0.102 s
% (2736)------------------------------
% (2736)------------------------------
fof(f272,plain,(
    ! [X2,X1] :
      ( ~ v7_waybel_0(k5_yellow_6(sK0,sK1,X2))
      | ~ m2_yellow_6(X1,sK0,k5_yellow_6(sK0,sK1,X2))
      | ~ v4_orders_2(k5_yellow_6(sK0,sK1,X2))
      | v2_struct_0(k5_yellow_6(sK0,sK1,X2))
      | l1_waybel_0(X1,sK0) ) ),
    inference(resolution,[],[f127,f157])).

fof(f127,plain,(
    ! [X21,X22] :
      ( ~ l1_waybel_0(X22,sK0)
      | ~ m2_yellow_6(X21,sK0,X22)
      | ~ v7_waybel_0(X22)
      | ~ v4_orders_2(X22)
      | v2_struct_0(X22)
      | l1_waybel_0(X21,sK0) ) ),
    inference(subsumption_resolution,[],[f113,f55])).

fof(f113,plain,(
    ! [X21,X22] :
      ( ~ m2_yellow_6(X21,sK0,X22)
      | ~ l1_waybel_0(X22,sK0)
      | ~ v7_waybel_0(X22)
      | ~ v4_orders_2(X22)
      | v2_struct_0(X22)
      | l1_waybel_0(X21,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | l1_waybel_0(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f530,plain,(
    v7_waybel_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))) ),
    inference(subsumption_resolution,[],[f529,f163])).

fof(f529,plain,
    ( v7_waybel_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))))
    | ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(resolution,[],[f472,f341])).

fof(f472,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v7_waybel_0(X0) ) ),
    inference(subsumption_resolution,[],[f471,f229])).

fof(f471,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v7_waybel_0(X0) ) ),
    inference(subsumption_resolution,[],[f468,f230])).

fof(f468,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | ~ v4_orders_2(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v7_waybel_0(X0) ) ),
    inference(resolution,[],[f206,f231])).

fof(f206,plain,(
    ! [X2,X1] :
      ( ~ v7_waybel_0(k5_yellow_6(sK0,sK1,X2))
      | ~ m2_yellow_6(X1,sK0,k5_yellow_6(sK0,sK1,X2))
      | ~ v4_orders_2(k5_yellow_6(sK0,sK1,X2))
      | v2_struct_0(k5_yellow_6(sK0,sK1,X2))
      | v7_waybel_0(X1) ) ),
    inference(resolution,[],[f126,f157])).

fof(f126,plain,(
    ! [X19,X20] :
      ( ~ l1_waybel_0(X20,sK0)
      | ~ m2_yellow_6(X19,sK0,X20)
      | ~ v7_waybel_0(X20)
      | ~ v4_orders_2(X20)
      | v2_struct_0(X20)
      | v7_waybel_0(X19) ) ),
    inference(subsumption_resolution,[],[f112,f55])).

fof(f112,plain,(
    ! [X19,X20] :
      ( ~ m2_yellow_6(X19,sK0,X20)
      | ~ l1_waybel_0(X20,sK0)
      | ~ v7_waybel_0(X20)
      | ~ v4_orders_2(X20)
      | v2_struct_0(X20)
      | v7_waybel_0(X19)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f85])).

fof(f519,plain,(
    v4_orders_2(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))) ),
    inference(subsumption_resolution,[],[f518,f163])).

fof(f518,plain,
    ( v4_orders_2(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))))
    | ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(resolution,[],[f458,f341])).

fof(f458,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v4_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f457,f229])).

fof(f457,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v4_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f454,f230])).

fof(f454,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | ~ v4_orders_2(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v4_orders_2(X0) ) ),
    inference(resolution,[],[f195,f231])).

fof(f195,plain,(
    ! [X2,X1] :
      ( ~ v7_waybel_0(k5_yellow_6(sK0,sK1,X2))
      | ~ m2_yellow_6(X1,sK0,k5_yellow_6(sK0,sK1,X2))
      | ~ v4_orders_2(k5_yellow_6(sK0,sK1,X2))
      | v2_struct_0(k5_yellow_6(sK0,sK1,X2))
      | v4_orders_2(X1) ) ),
    inference(resolution,[],[f125,f157])).

fof(f125,plain,(
    ! [X17,X18] :
      ( ~ l1_waybel_0(X18,sK0)
      | ~ m2_yellow_6(X17,sK0,X18)
      | ~ v7_waybel_0(X18)
      | ~ v4_orders_2(X18)
      | v2_struct_0(X18)
      | v4_orders_2(X17) ) ),
    inference(subsumption_resolution,[],[f111,f55])).

fof(f111,plain,(
    ! [X17,X18] :
      ( ~ m2_yellow_6(X17,sK0,X18)
      | ~ l1_waybel_0(X18,sK0)
      | ~ v7_waybel_0(X18)
      | ~ v4_orders_2(X18)
      | v2_struct_0(X18)
      | v4_orders_2(X17)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f84])).

fof(f508,plain,(
    ~ v2_struct_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))) ),
    inference(subsumption_resolution,[],[f507,f163])).

fof(f507,plain,
    ( ~ v2_struct_0(sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))))
    | ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))) ),
    inference(resolution,[],[f444,f341])).

fof(f444,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | ~ v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f443,f229])).

fof(f443,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | ~ v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f440,f230])).

fof(f440,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | ~ v4_orders_2(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | v2_struct_0(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))
      | ~ v2_struct_0(X0) ) ),
    inference(resolution,[],[f186,f231])).

fof(f186,plain,(
    ! [X2,X1] :
      ( ~ v7_waybel_0(k5_yellow_6(sK0,sK1,X2))
      | ~ m2_yellow_6(X1,sK0,k5_yellow_6(sK0,sK1,X2))
      | ~ v4_orders_2(k5_yellow_6(sK0,sK1,X2))
      | v2_struct_0(k5_yellow_6(sK0,sK1,X2))
      | ~ v2_struct_0(X1) ) ),
    inference(resolution,[],[f124,f157])).

fof(f124,plain,(
    ! [X15,X16] :
      ( ~ l1_waybel_0(X16,sK0)
      | ~ m2_yellow_6(X15,sK0,X16)
      | ~ v7_waybel_0(X16)
      | ~ v4_orders_2(X16)
      | v2_struct_0(X16)
      | ~ v2_struct_0(X15) ) ),
    inference(subsumption_resolution,[],[f110,f55])).

fof(f110,plain,(
    ! [X15,X16] :
      ( ~ m2_yellow_6(X15,sK0,X16)
      | ~ l1_waybel_0(X16,sK0)
      | ~ v7_waybel_0(X16)
      | ~ v4_orders_2(X16)
      | v2_struct_0(X16)
      | ~ v2_struct_0(X15)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f83])).

fof(f93,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f740,plain,(
    r1_waybel_0(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))),sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f131,f62,f508,f519,f530,f561,f224,f569,f91])).

fof(f91,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r1_waybel_0(X0,X1,X8)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f569,plain,(
    m1_subset_1(k10_yellow_6(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f508,f519,f530,f561,f82])).

fof(f224,plain,(
    r2_hidden(sK2,k10_yellow_6(sK0,sK3(k5_yellow_6(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,sK2)))))) ),
    inference(unit_resulting_resolution,[],[f184,f65])).

fof(f65,plain,(
    ! [X3] :
      ( r2_hidden(sK2,k10_yellow_6(sK0,sK3(X3)))
      | ~ m2_yellow_6(X3,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f131,plain,(
    m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f58,f59,f60,f61,f62,f63,f129,f90])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_connsp_2(sK6(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f52])).

%------------------------------------------------------------------------------
