%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:45 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 939 expanded)
%              Number of leaves         :   16 ( 347 expanded)
%              Depth                    :   52
%              Number of atoms          : 1089 (7861 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :   20 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(subsumption_resolution,[],[f227,f48])).

fof(f48,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
    & m2_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
                & m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(sK0,X1),k10_yellow_6(sK0,X2))
              & m2_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k10_yellow_6(sK0,X1),k10_yellow_6(sK0,X2))
            & m2_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,X2))
          & m2_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,X2))
        & m2_yellow_6(X2,sK0,sK1) )
   => ( ~ r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
      & m2_yellow_6(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
                ( m2_yellow_6(X2,X0,X1)
               => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
              ( m2_yellow_6(X2,X0,X1)
             => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_yellow_6)).

fof(f227,plain,(
    ~ l1_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f226,f47])).

fof(f47,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f226,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f225,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f225,plain,
    ( v2_struct_0(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f224,f46])).

fof(f46,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f224,plain,
    ( ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0) ),
    inference(resolution,[],[f223,f49])).

fof(f49,plain,(
    m2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f223,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(sK2,sK0,X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f222,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f222,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_yellow_6(sK2,sK0,X0)
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f221,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_yellow_6(sK2,X1,X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f220,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m2_yellow_6(sK2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f219,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f219,plain,(
    v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f218,f50])).

fof(f50,plain,(
    ~ r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f218,plain,
    ( r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
    | v2_struct_0(sK2)
    | r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) ),
    inference(resolution,[],[f214,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f214,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f212,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f212,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f210,f128])).

fof(f128,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f125,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f125,plain,(
    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f124,plain,
    ( v2_struct_0(sK1)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f123,f46])).

fof(f123,plain,
    ( ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f121,f48])).

fof(f121,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f120,f47])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k10_yellow_6(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f119,f42])).

fof(f119,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k10_yellow_6(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f118,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(k10_yellow_6(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f210,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0))
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f209,f42])).

fof(f209,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f208,f43])).

fof(f208,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f207,f44])).

fof(f207,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f206,f106])).

fof(f106,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(resolution,[],[f105,f49])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,sK1)
      | l1_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | l1_waybel_0(X0,sK0)
      | ~ m2_yellow_6(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f103,f46])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | l1_waybel_0(X0,sK0)
      | ~ m2_yellow_6(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | l1_waybel_0(X0,sK0)
      | ~ m2_yellow_6(X0,sK0,sK1) ) ),
    inference(resolution,[],[f101,f48])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | l1_waybel_0(X1,sK0)
      | ~ m2_yellow_6(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | l1_waybel_0(X1,sK0)
      | v2_struct_0(sK0)
      | ~ m2_yellow_6(X1,sK0,X0) ) ),
    inference(resolution,[],[f98,f44])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | l1_waybel_0(X0,X1)
      | v2_struct_0(X1)
      | ~ m2_yellow_6(X0,X1,X2) ) ),
    inference(resolution,[],[f64,f66])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | l1_waybel_0(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f206,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | ~ l1_waybel_0(sK2,sK0)
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f205,f85])).

fof(f85,plain,(
    v4_orders_2(sK2) ),
    inference(resolution,[],[f84,f49])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,sK1)
      | v4_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f83,f44])).

fof(f83,plain,(
    ! [X0] :
      ( v4_orders_2(X0)
      | ~ m2_yellow_6(X0,sK0,sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f82,f66])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v4_orders_2(X0)
      | ~ m2_yellow_6(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,sK1)
      | v4_orders_2(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f80,f48])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK1,X1)
      | ~ m2_yellow_6(X0,X1,sK1)
      | v4_orders_2(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m2_yellow_6(X0,X1,sK1)
      | ~ l1_waybel_0(sK1,X1)
      | v4_orders_2(X0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m2_yellow_6(X0,X1,sK1)
      | ~ l1_waybel_0(sK1,X1)
      | v4_orders_2(X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f62,f47])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v4_orders_2(X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f205,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | ~ l1_waybel_0(sK2,sK0)
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f204,f93])).

fof(f93,plain,(
    v7_waybel_0(sK2) ),
    inference(resolution,[],[f92,f49])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,sK1)
      | v7_waybel_0(X0) ) ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f91,plain,(
    ! [X0] :
      ( v7_waybel_0(X0)
      | ~ m2_yellow_6(X0,sK0,sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f90,f66])).

fof(f90,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v7_waybel_0(X0)
      | ~ m2_yellow_6(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f89,f42])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,sK1)
      | v7_waybel_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f88,f48])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK1,X1)
      | ~ m2_yellow_6(X0,X1,sK1)
      | v7_waybel_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f87,f45])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m2_yellow_6(X0,X1,sK1)
      | ~ l1_waybel_0(sK1,X1)
      | v7_waybel_0(X0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f86,f46])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m2_yellow_6(X0,X1,sK1)
      | ~ l1_waybel_0(sK1,X1)
      | v7_waybel_0(X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v7_waybel_0(X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f204,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | ~ l1_waybel_0(sK2,sK0)
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | v2_struct_0(sK2)
      | ~ l1_waybel_0(sK2,sK0)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2))
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f202,f73])).

fof(f73,plain,(
    ! [X6,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f70,f53])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK4(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
        & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
        & m1_connsp_2(sK6(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f202,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK0,sK2,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1)))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | v2_struct_0(sK2)
      | ~ l1_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f201,f106])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | v2_struct_0(sK2)
      | r1_waybel_0(sK0,sK2,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1)))
      | ~ l1_waybel_0(sK2,sK0) ) ),
    inference(resolution,[],[f200,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,X1)
      | ~ l1_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,X1)
      | v2_struct_0(sK0)
      | r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) ) ),
    inference(resolution,[],[f99,f44])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ),
    inference(resolution,[],[f69,f66])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),sK6(sK0,X1,sK3(k10_yellow_6(sK0,sK1),X0))))
      | ~ l1_waybel_0(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,X1))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f199,f44])).

fof(f199,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,X1))
      | ~ l1_waybel_0(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),sK6(sK0,X1,sK3(k10_yellow_6(sK0,sK1),X0))))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f196,f66])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,X1))
      | ~ l1_waybel_0(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),sK6(sK0,X1,sK3(k10_yellow_6(sK0,sK1),X0))))
      | r1_tarski(k10_yellow_6(sK0,sK1),X0) ) ),
    inference(resolution,[],[f195,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK1,X0)
      | ~ r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f42])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f45])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_waybel_0(sK0,sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f137,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f137,plain,(
    ! [X0] :
      ( r2_waybel_0(sK0,sK1,X0)
      | ~ r2_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f136,f45])).

fof(f136,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X0)
      | ~ r2_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f135,f46])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X0)
      | ~ r2_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f134,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X0)
      | ~ r2_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f133,f48])).

fof(f133,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X0)
      | ~ r2_waybel_0(sK0,sK2,X0) ) ),
    inference(resolution,[],[f132,f49])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X0,sK0,X1)
      | ~ l1_waybel_0(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r2_waybel_0(sK0,X1,X2)
      | ~ r2_waybel_0(sK0,X0,X2) ) ),
    inference(subsumption_resolution,[],[f131,f42])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X0,sK0,X1)
      | ~ l1_waybel_0(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r2_waybel_0(sK0,X1,X2)
      | v2_struct_0(sK0)
      | ~ r2_waybel_0(sK0,X0,X2) ) ),
    inference(resolution,[],[f130,f44])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m2_yellow_6(X1,X0,X3)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | r2_waybel_0(X0,X3,X2)
      | v2_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(resolution,[],[f65,f66])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f195,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1)))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f194,f48])).

fof(f194,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1)))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f193,f45])).

fof(f193,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1)))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f192,f46])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1)))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f191,f47])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1)))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1)))
      | r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,sK0)
      | r1_tarski(k10_yellow_6(sK0,sK1),X1) ) ),
    inference(resolution,[],[f189,f51])).

fof(f189,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(k10_yellow_6(sK0,X3),X5),k10_yellow_6(sK0,sK1))
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | r1_waybel_0(sK0,X3,sK6(sK0,X4,sK3(k10_yellow_6(sK0,X3),X5)))
      | r1_tarski(k10_yellow_6(sK0,X3),X5)
      | r2_hidden(sK3(k10_yellow_6(sK0,X3),X5),k10_yellow_6(sK0,X4))
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_waybel_0(X3,sK0) ) ),
    inference(resolution,[],[f160,f128])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1)))
      | r1_tarski(k10_yellow_6(sK0,X0),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f159,f42])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1)))
      | r1_tarski(k10_yellow_6(sK0,X0),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f43])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1)))
      | r1_tarski(k10_yellow_6(sK0,X0),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f44])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1)))
      | r1_tarski(k10_yellow_6(sK0,X0),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1)))
      | r1_tarski(k10_yellow_6(sK0,X0),X1)
      | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2))
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f155,f74])).

% (427)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f74,plain,(
    ! [X6,X0,X1] :
      ( m1_connsp_2(sK6(X0,X1,X6),X0,X6)
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f71,f53])).

fof(f71,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK6(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,sK3(k10_yellow_6(sK0,X1),X2))
      | ~ m1_subset_1(sK3(k10_yellow_6(sK0,X1),X2),u1_struct_0(sK0))
      | ~ l1_waybel_0(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r1_waybel_0(sK0,X1,X0)
      | r1_tarski(k10_yellow_6(sK0,X1),X2) ) ),
    inference(resolution,[],[f154,f51])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k10_yellow_6(sK0,X2))
      | ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | r1_waybel_0(sK0,X2,X0) ) ),
    inference(subsumption_resolution,[],[f153,f42])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | r1_waybel_0(sK0,X2,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f44])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | r1_waybel_0(sK0,X2,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f75,f43])).

fof(f75,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_waybel_0(X0,X1,X8)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f72,f53])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.17/0.52  % (425)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.17/0.52  % (429)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (436)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.52  % (446)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.17/0.52  % (438)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.53  % (440)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.17/0.53  % (445)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.17/0.53  % (428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.53  % (433)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.54  % (449)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  % (429)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.54  fof(f228,plain,(
% 1.38/0.54    $false),
% 1.38/0.54    inference(subsumption_resolution,[],[f227,f48])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    l1_waybel_0(sK1,sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ((~r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) & m2_yellow_6(sK2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f30,f29,f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(sK0,X1),k10_yellow_6(sK0,X2)) & m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(sK0,X1),k10_yellow_6(sK0,X2)) & m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,X2)) & m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    ? [X2] : (~r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,X2)) & m2_yellow_6(X2,sK0,sK1)) => (~r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) & m2_yellow_6(sK2,sK0,sK1))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f13,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f12])).
% 1.38/0.54  fof(f12,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f10])).
% 1.38/0.54  fof(f10,negated_conjecture,(
% 1.38/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)))))),
% 1.38/0.54    inference(negated_conjecture,[],[f9])).
% 1.38/0.54  fof(f9,conjecture,(
% 1.38/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_yellow_6)).
% 1.38/0.54  fof(f227,plain,(
% 1.38/0.54    ~l1_waybel_0(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f226,f47])).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    v7_waybel_0(sK1)),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f226,plain,(
% 1.38/0.54    ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f225,f45])).
% 1.38/0.54  fof(f45,plain,(
% 1.38/0.54    ~v2_struct_0(sK1)),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f225,plain,(
% 1.38/0.54    v2_struct_0(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f224,f46])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    v4_orders_2(sK1)),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f224,plain,(
% 1.38/0.54    ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0)),
% 1.38/0.54    inference(resolution,[],[f223,f49])).
% 1.38/0.54  fof(f49,plain,(
% 1.38/0.54    m2_yellow_6(sK2,sK0,sK1)),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f223,plain,(
% 1.38/0.54    ( ! [X0] : (~m2_yellow_6(sK2,sK0,X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f222,f42])).
% 1.38/0.54  fof(f42,plain,(
% 1.38/0.54    ~v2_struct_0(sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f222,plain,(
% 1.38/0.54    ( ! [X0] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m2_yellow_6(sK2,sK0,X0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0)) )),
% 1.38/0.54    inference(resolution,[],[f221,f44])).
% 1.38/0.54  fof(f44,plain,(
% 1.38/0.54    l1_pre_topc(sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f221,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m2_yellow_6(sK2,X1,X0) | v2_struct_0(X1) | ~l1_waybel_0(X0,X1)) )),
% 1.38/0.54    inference(resolution,[],[f220,f66])).
% 1.38/0.54  fof(f66,plain,(
% 1.38/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f23])).
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.38/0.54  fof(f220,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~m2_yellow_6(sK2,X0,X1) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(resolution,[],[f219,f61])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,plain,(
% 1.38/0.54    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f19])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 1.38/0.54  fof(f219,plain,(
% 1.38/0.54    v2_struct_0(sK2)),
% 1.38/0.54    inference(subsumption_resolution,[],[f218,f50])).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    ~r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f218,plain,(
% 1.38/0.54    r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) | v2_struct_0(sK2)),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f215])).
% 1.38/0.54  fof(f215,plain,(
% 1.38/0.54    r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) | v2_struct_0(sK2) | r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))),
% 1.38/0.54    inference(resolution,[],[f214,f52])).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f33])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f32])).
% 1.38/0.54  fof(f32,plain,(
% 1.38/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f14,plain,(
% 1.38/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,plain,(
% 1.38/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.38/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.38/0.54  fof(f1,axiom,(
% 1.38/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.54  fof(f214,plain,(
% 1.38/0.54    ( ! [X1] : (r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | v2_struct_0(sK2)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f212,f51])).
% 1.38/0.54  fof(f51,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f33])).
% 1.38/0.54  fof(f212,plain,(
% 1.38/0.54    ( ! [X1] : (r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | v2_struct_0(sK2) | ~r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,sK1))) )),
% 1.38/0.54    inference(resolution,[],[f210,f128])).
% 1.38/0.54  fof(f128,plain,(
% 1.38/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1))) )),
% 1.38/0.54    inference(resolution,[],[f125,f67])).
% 1.38/0.54  fof(f67,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f25])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.38/0.54    inference(flattening,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.38/0.54    inference(ennf_transformation,[],[f2])).
% 1.38/0.54  fof(f2,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.38/0.54  fof(f125,plain,(
% 1.38/0.54    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(subsumption_resolution,[],[f124,f45])).
% 1.38/0.54  fof(f124,plain,(
% 1.38/0.54    v2_struct_0(sK1) | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(subsumption_resolution,[],[f123,f46])).
% 1.38/0.54  fof(f123,plain,(
% 1.38/0.54    ~v4_orders_2(sK1) | v2_struct_0(sK1) | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(subsumption_resolution,[],[f121,f48])).
% 1.38/0.54  fof(f121,plain,(
% 1.38/0.54    ~l1_waybel_0(sK1,sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(resolution,[],[f120,f47])).
% 1.38/0.54  fof(f120,plain,(
% 1.38/0.54    ( ! [X0] : (~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~v4_orders_2(X0) | v2_struct_0(X0) | m1_subset_1(k10_yellow_6(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f119,f42])).
% 1.38/0.54  fof(f119,plain,(
% 1.38/0.54    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | m1_subset_1(k10_yellow_6(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f118,f44])).
% 1.38/0.54  fof(f118,plain,(
% 1.38/0.54    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | m1_subset_1(k10_yellow_6(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f53,f43])).
% 1.38/0.54  fof(f43,plain,(
% 1.38/0.54    v2_pre_topc(sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f53,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f16])).
% 1.38/0.54  fof(f16,plain,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f15])).
% 1.38/0.54  fof(f15,plain,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 1.38/0.54  fof(f210,plain,(
% 1.38/0.54    ( ! [X0] : (~m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0)) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | v2_struct_0(sK2)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f209,f42])).
% 1.38/0.54  fof(f209,plain,(
% 1.38/0.54    ( ! [X0] : (v2_struct_0(sK2) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | ~m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f208,f43])).
% 1.38/0.54  fof(f208,plain,(
% 1.38/0.54    ( ! [X0] : (v2_struct_0(sK2) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | ~m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f207,f44])).
% 1.38/0.54  fof(f207,plain,(
% 1.38/0.54    ( ! [X0] : (v2_struct_0(sK2) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | ~m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f206,f106])).
% 1.38/0.54  fof(f106,plain,(
% 1.38/0.54    l1_waybel_0(sK2,sK0)),
% 1.38/0.54    inference(resolution,[],[f105,f49])).
% 1.38/0.54  fof(f105,plain,(
% 1.38/0.54    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | l1_waybel_0(X0,sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f104,f45])).
% 1.38/0.54  fof(f104,plain,(
% 1.38/0.54    ( ! [X0] : (v2_struct_0(sK1) | l1_waybel_0(X0,sK0) | ~m2_yellow_6(X0,sK0,sK1)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f103,f46])).
% 1.38/0.54  fof(f103,plain,(
% 1.38/0.54    ( ! [X0] : (~v4_orders_2(sK1) | v2_struct_0(sK1) | l1_waybel_0(X0,sK0) | ~m2_yellow_6(X0,sK0,sK1)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f102,f47])).
% 1.38/0.54  fof(f102,plain,(
% 1.38/0.54    ( ! [X0] : (~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | l1_waybel_0(X0,sK0) | ~m2_yellow_6(X0,sK0,sK1)) )),
% 1.38/0.54    inference(resolution,[],[f101,f48])).
% 1.38/0.54  fof(f101,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | l1_waybel_0(X1,sK0) | ~m2_yellow_6(X1,sK0,X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f100,f42])).
% 1.38/0.54  fof(f100,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | l1_waybel_0(X1,sK0) | v2_struct_0(sK0) | ~m2_yellow_6(X1,sK0,X0)) )),
% 1.38/0.54    inference(resolution,[],[f98,f44])).
% 1.38/0.54  fof(f98,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | l1_waybel_0(X0,X1) | v2_struct_0(X1) | ~m2_yellow_6(X0,X1,X2)) )),
% 1.38/0.54    inference(resolution,[],[f64,f66])).
% 1.38/0.54  fof(f64,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | l1_waybel_0(X2,X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f206,plain,(
% 1.38/0.54    ( ! [X0] : (v2_struct_0(sK2) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f205,f85])).
% 1.38/0.54  fof(f85,plain,(
% 1.38/0.54    v4_orders_2(sK2)),
% 1.38/0.54    inference(resolution,[],[f84,f49])).
% 1.38/0.54  fof(f84,plain,(
% 1.38/0.54    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | v4_orders_2(X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f83,f44])).
% 1.38/0.54  fof(f83,plain,(
% 1.38/0.54    ( ! [X0] : (v4_orders_2(X0) | ~m2_yellow_6(X0,sK0,sK1) | ~l1_pre_topc(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f82,f66])).
% 1.38/0.54  fof(f82,plain,(
% 1.38/0.54    ( ! [X0] : (~l1_struct_0(sK0) | v4_orders_2(X0) | ~m2_yellow_6(X0,sK0,sK1)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f81,f42])).
% 1.38/0.54  fof(f81,plain,(
% 1.38/0.54    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | v4_orders_2(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f80,f48])).
% 1.38/0.54  fof(f80,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_waybel_0(sK1,X1) | ~m2_yellow_6(X0,X1,sK1) | v4_orders_2(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f79,f45])).
% 1.38/0.54  fof(f79,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m2_yellow_6(X0,X1,sK1) | ~l1_waybel_0(sK1,X1) | v4_orders_2(X0) | v2_struct_0(sK1) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f78,f46])).
% 1.38/0.54  fof(f78,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m2_yellow_6(X0,X1,sK1) | ~l1_waybel_0(sK1,X1) | v4_orders_2(X0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.38/0.54    inference(resolution,[],[f62,f47])).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | v4_orders_2(X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f205,plain,(
% 1.38/0.54    ( ! [X0] : (~v4_orders_2(sK2) | v2_struct_0(sK2) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f204,f93])).
% 1.38/0.54  fof(f93,plain,(
% 1.38/0.54    v7_waybel_0(sK2)),
% 1.38/0.54    inference(resolution,[],[f92,f49])).
% 1.38/0.54  fof(f92,plain,(
% 1.38/0.54    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | v7_waybel_0(X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f91,f44])).
% 1.38/0.54  fof(f91,plain,(
% 1.38/0.54    ( ! [X0] : (v7_waybel_0(X0) | ~m2_yellow_6(X0,sK0,sK1) | ~l1_pre_topc(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f90,f66])).
% 1.38/0.54  fof(f90,plain,(
% 1.38/0.54    ( ! [X0] : (~l1_struct_0(sK0) | v7_waybel_0(X0) | ~m2_yellow_6(X0,sK0,sK1)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f89,f42])).
% 1.38/0.54  fof(f89,plain,(
% 1.38/0.54    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | v7_waybel_0(X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f88,f48])).
% 1.38/0.54  fof(f88,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_waybel_0(sK1,X1) | ~m2_yellow_6(X0,X1,sK1) | v7_waybel_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f87,f45])).
% 1.38/0.54  fof(f87,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m2_yellow_6(X0,X1,sK1) | ~l1_waybel_0(sK1,X1) | v7_waybel_0(X0) | v2_struct_0(sK1) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f86,f46])).
% 1.38/0.54  fof(f86,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m2_yellow_6(X0,X1,sK1) | ~l1_waybel_0(sK1,X1) | v7_waybel_0(X0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.38/0.54    inference(resolution,[],[f63,f47])).
% 1.38/0.54  fof(f63,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | v7_waybel_0(X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f204,plain,(
% 1.38/0.54    ( ! [X0] : (~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f203])).
% 1.38/0.54  fof(f203,plain,(
% 1.38/0.54    ( ! [X0] : (~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | v2_struct_0(sK2) | ~l1_waybel_0(sK2,sK0) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,sK2)) | ~m1_subset_1(sK3(k10_yellow_6(sK0,sK1),X0),u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f202,f73])).
% 1.38/0.54  fof(f73,plain,(
% 1.38/0.54    ( ! [X6,X0,X1] : (~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f70,f53])).
% 1.38/0.54  fof(f70,plain,(
% 1.38/0.54    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(equality_resolution,[],[f56])).
% 1.38/0.54  fof(f56,plain,(
% 1.38/0.54    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f40])).
% 1.38/0.54  fof(f40,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK5(X0,X1,X2)) & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK4(X0,X1,X2))) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) & m1_connsp_2(sK6(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK4(X0,X1,X2))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK4(X0,X1,X2))) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f38,plain,(
% 1.38/0.54    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK4(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK5(X0,X1,X2)) & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK6(X0,X1,X6)) & m1_connsp_2(sK6(X0,X1,X6),X0,X6)))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(rectify,[],[f35])).
% 1.38/0.54  fof(f35,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f34])).
% 1.38/0.54  fof(f34,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f18])).
% 1.38/0.54  fof(f18,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f17])).
% 1.38/0.54  fof(f17,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).
% 1.38/0.54  fof(f202,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_waybel_0(sK0,sK2,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1))) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0)) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | v2_struct_0(sK2) | ~l1_waybel_0(X0,sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f201,f106])).
% 1.38/0.54  fof(f201,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0)) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | v2_struct_0(sK2) | r1_waybel_0(sK0,sK2,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1))) | ~l1_waybel_0(sK2,sK0)) )),
% 1.38/0.54    inference(resolution,[],[f200,f115])).
% 1.38/0.54  fof(f115,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,X1) | ~l1_waybel_0(X0,sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f114,f42])).
% 1.38/0.54  fof(f114,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,X1) | v2_struct_0(sK0) | r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))) )),
% 1.38/0.54    inference(resolution,[],[f99,f44])).
% 1.38/0.54  fof(f99,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r1_waybel_0(X0,X1,X2) | v2_struct_0(X0) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) )),
% 1.38/0.54    inference(resolution,[],[f69,f66])).
% 1.38/0.54  fof(f69,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r1_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f41])).
% 1.38/0.54  fof(f41,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f27])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).
% 1.38/0.54  fof(f200,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),sK6(sK0,X1,sK3(k10_yellow_6(sK0,sK1),X0)))) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,X1)) | r1_tarski(k10_yellow_6(sK0,sK1),X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f199,f44])).
% 1.38/0.54  fof(f199,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,X1)) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),sK6(sK0,X1,sK3(k10_yellow_6(sK0,sK1),X0)))) | r1_tarski(k10_yellow_6(sK0,sK1),X0) | ~l1_pre_topc(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f196,f66])).
% 1.38/0.54  fof(f196,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~l1_struct_0(sK0) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X0),k10_yellow_6(sK0,X1)) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),sK6(sK0,X1,sK3(k10_yellow_6(sK0,sK1),X0)))) | r1_tarski(k10_yellow_6(sK0,sK1),X0)) )),
% 1.38/0.54    inference(resolution,[],[f195,f141])).
% 1.38/0.54  fof(f141,plain,(
% 1.38/0.54    ( ! [X0] : (~r1_waybel_0(sK0,sK1,X0) | ~r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),X0)) | ~l1_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f140,f42])).
% 1.38/0.54  fof(f140,plain,(
% 1.38/0.54    ( ! [X0] : (~r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),X0)) | ~r1_waybel_0(sK0,sK1,X0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f139,f45])).
% 1.38/0.54  fof(f139,plain,(
% 1.38/0.54    ( ! [X0] : (~r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),X0)) | ~r1_waybel_0(sK0,sK1,X0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f138,f48])).
% 1.38/0.54  fof(f138,plain,(
% 1.38/0.54    ( ! [X0] : (~r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),X0)) | ~r1_waybel_0(sK0,sK1,X0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f137,f68])).
% 1.38/0.54  fof(f68,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f41])).
% 1.38/0.54  fof(f137,plain,(
% 1.38/0.54    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0) | ~r2_waybel_0(sK0,sK2,X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f136,f45])).
% 1.38/0.54  fof(f136,plain,(
% 1.38/0.54    ( ! [X0] : (v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X0) | ~r2_waybel_0(sK0,sK2,X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f135,f46])).
% 1.38/0.54  fof(f135,plain,(
% 1.38/0.54    ( ! [X0] : (~v4_orders_2(sK1) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X0) | ~r2_waybel_0(sK0,sK2,X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f134,f47])).
% 1.38/0.54  fof(f134,plain,(
% 1.38/0.54    ( ! [X0] : (~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X0) | ~r2_waybel_0(sK0,sK2,X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f133,f48])).
% 1.38/0.54  fof(f133,plain,(
% 1.38/0.54    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X0) | ~r2_waybel_0(sK0,sK2,X0)) )),
% 1.38/0.54    inference(resolution,[],[f132,f49])).
% 1.38/0.54  fof(f132,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m2_yellow_6(X0,sK0,X1) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_waybel_0(sK0,X1,X2) | ~r2_waybel_0(sK0,X0,X2)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f131,f42])).
% 1.38/0.54  fof(f131,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m2_yellow_6(X0,sK0,X1) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_waybel_0(sK0,X1,X2) | v2_struct_0(sK0) | ~r2_waybel_0(sK0,X0,X2)) )),
% 1.38/0.54    inference(resolution,[],[f130,f44])).
% 1.38/0.54  fof(f130,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m2_yellow_6(X1,X0,X3) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | r2_waybel_0(X0,X3,X2) | v2_struct_0(X0) | ~r2_waybel_0(X0,X1,X2)) )),
% 1.38/0.54    inference(resolution,[],[f65,f66])).
% 1.38/0.54  fof(f65,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X3) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f22])).
% 1.38/0.54  fof(f22,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f21])).
% 1.38/0.54  fof(f21,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).
% 1.38/0.54  fof(f195,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1))) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f194,f48])).
% 1.38/0.54  fof(f194,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1))) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(sK1,sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f193,f45])).
% 1.38/0.54  fof(f193,plain,(
% 1.38/0.54    ( ! [X0,X1] : (v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1))) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(sK1,sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f192,f46])).
% 1.38/0.54  fof(f192,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~v4_orders_2(sK1) | v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1))) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(sK1,sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f191,f47])).
% 1.38/0.54  fof(f191,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1))) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(sK1,sK0)) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f190])).
% 1.38/0.54  fof(f190,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,sK6(sK0,X0,sK3(k10_yellow_6(sK0,sK1),X1))) | r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(sK3(k10_yellow_6(sK0,sK1),X1),k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(sK1,sK0) | r1_tarski(k10_yellow_6(sK0,sK1),X1)) )),
% 1.38/0.54    inference(resolution,[],[f189,f51])).
% 1.38/0.54  fof(f189,plain,(
% 1.38/0.54    ( ! [X4,X5,X3] : (~r2_hidden(sK3(k10_yellow_6(sK0,X3),X5),k10_yellow_6(sK0,sK1)) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | r1_waybel_0(sK0,X3,sK6(sK0,X4,sK3(k10_yellow_6(sK0,X3),X5))) | r1_tarski(k10_yellow_6(sK0,X3),X5) | r2_hidden(sK3(k10_yellow_6(sK0,X3),X5),k10_yellow_6(sK0,X4)) | ~l1_waybel_0(X4,sK0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~l1_waybel_0(X3,sK0)) )),
% 1.38/0.54    inference(resolution,[],[f160,f128])).
% 1.38/0.54  fof(f160,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1))) | r1_tarski(k10_yellow_6(sK0,X0),X1) | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f159,f42])).
% 1.38/0.54  fof(f159,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1))) | r1_tarski(k10_yellow_6(sK0,X0),X1) | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f158,f43])).
% 1.38/0.54  fof(f158,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1))) | r1_tarski(k10_yellow_6(sK0,X0),X1) | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f157,f44])).
% 1.38/0.54  fof(f157,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1))) | r1_tarski(k10_yellow_6(sK0,X0),X1) | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f156])).
% 1.38/0.54  fof(f156,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,sK6(sK0,X2,sK3(k10_yellow_6(sK0,X0),X1))) | r1_tarski(k10_yellow_6(sK0,X0),X1) | r2_hidden(sK3(k10_yellow_6(sK0,X0),X1),k10_yellow_6(sK0,X2)) | ~m1_subset_1(sK3(k10_yellow_6(sK0,X0),X1),u1_struct_0(sK0)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f155,f74])).
% 1.38/0.54  % (427)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  fof(f74,plain,(
% 1.38/0.54    ( ! [X6,X0,X1] : (m1_connsp_2(sK6(X0,X1,X6),X0,X6) | r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f71,f53])).
% 1.38/0.54  fof(f71,plain,(
% 1.38/0.54    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK6(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(equality_resolution,[],[f55])).
% 1.38/0.54  fof(f55,plain,(
% 1.38/0.54    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK6(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f40])).
% 1.38/0.54  fof(f155,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK0,sK3(k10_yellow_6(sK0,X1),X2)) | ~m1_subset_1(sK3(k10_yellow_6(sK0,X1),X2),u1_struct_0(sK0)) | ~l1_waybel_0(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | r1_waybel_0(sK0,X1,X0) | r1_tarski(k10_yellow_6(sK0,X1),X2)) )),
% 1.38/0.54    inference(resolution,[],[f154,f51])).
% 1.38/0.54  fof(f154,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,k10_yellow_6(sK0,X2)) | ~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | r1_waybel_0(sK0,X2,X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f153,f42])).
% 1.38/0.54  fof(f153,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | r1_waybel_0(sK0,X2,X0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f152,f44])).
% 1.38/0.54  fof(f152,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | r1_waybel_0(sK0,X2,X0) | v2_struct_0(sK0)) )),
% 1.38/0.54    inference(resolution,[],[f75,f43])).
% 1.38/0.54  fof(f75,plain,(
% 1.38/0.54    ( ! [X6,X0,X8,X1] : (~v2_pre_topc(X0) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_waybel_0(X0,X1,X8) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f72,f53])).
% 1.38/0.54  fof(f72,plain,(
% 1.38/0.54    ( ! [X6,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(equality_resolution,[],[f54])).
% 1.38/0.54  fof(f54,plain,(
% 1.38/0.54    ( ! [X6,X2,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f40])).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (429)------------------------------
% 1.38/0.54  % (429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (429)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (429)Memory used [KB]: 6396
% 1.38/0.54  % (429)Time elapsed: 0.131 s
% 1.38/0.54  % (429)------------------------------
% 1.38/0.54  % (429)------------------------------
% 1.38/0.54  % (424)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.54  % (430)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.54  % (433)Refutation not found, incomplete strategy% (433)------------------------------
% 1.38/0.54  % (433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (433)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (433)Memory used [KB]: 10874
% 1.38/0.54  % (433)Time elapsed: 0.139 s
% 1.38/0.54  % (433)------------------------------
% 1.38/0.54  % (433)------------------------------
% 1.38/0.54  % (434)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.54  % (444)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.54  % (448)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.54  % (452)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (426)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.54  % (431)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.54  % (443)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (439)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.55  % (451)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (453)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.55  % (450)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (415)Success in time 0.189 s
%------------------------------------------------------------------------------
