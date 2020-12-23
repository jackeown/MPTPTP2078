%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1947+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 250 expanded)
%              Number of leaves         :    8 (  89 expanded)
%              Depth                    :    8
%              Number of atoms          :  263 (2495 expanded)
%              Number of equality atoms :   16 ( 259 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9371,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9269,f6091])).

fof(f6091,plain,(
    m1_subset_1(k4_yellow_6(sK38,sK39),u1_struct_0(sK38)) ),
    inference(unit_resulting_resolution,[],[f5109,f5117,f6029,f5122])).

fof(f5122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4075])).

fof(f4075,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4074])).

fof(f4074,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3858])).

fof(f3858,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(f6029,plain,(
    l1_struct_0(sK38) ),
    inference(unit_resulting_resolution,[],[f5112,f5223])).

fof(f5223,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4129])).

fof(f4129,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f5112,plain,(
    l1_pre_topc(sK38) ),
    inference(cnf_transformation,[],[f4714])).

fof(f4714,plain,
    ( k4_yellow_6(sK38,sK39) != k11_yellow_6(sK38,sK39)
    & l1_waybel_0(sK39,sK38)
    & v1_yellow_6(sK39,sK38)
    & v7_waybel_0(sK39)
    & v4_orders_2(sK39)
    & ~ v2_struct_0(sK39)
    & l1_pre_topc(sK38)
    & v8_pre_topc(sK38)
    & v2_pre_topc(sK38)
    & ~ v2_struct_0(sK38) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK38,sK39])],[f4069,f4713,f4712])).

fof(f4712,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_yellow_6(X0,X1) != k11_yellow_6(X0,X1)
            & l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_yellow_6(sK38,X1) != k11_yellow_6(sK38,X1)
          & l1_waybel_0(X1,sK38)
          & v1_yellow_6(X1,sK38)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK38)
      & v8_pre_topc(sK38)
      & v2_pre_topc(sK38)
      & ~ v2_struct_0(sK38) ) ),
    introduced(choice_axiom,[])).

fof(f4713,plain,
    ( ? [X1] :
        ( k4_yellow_6(sK38,X1) != k11_yellow_6(sK38,X1)
        & l1_waybel_0(X1,sK38)
        & v1_yellow_6(X1,sK38)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( k4_yellow_6(sK38,sK39) != k11_yellow_6(sK38,sK39)
      & l1_waybel_0(sK39,sK38)
      & v1_yellow_6(sK39,sK38)
      & v7_waybel_0(sK39)
      & v4_orders_2(sK39)
      & ~ v2_struct_0(sK39) ) ),
    introduced(choice_axiom,[])).

fof(f4069,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_yellow_6(X0,X1) != k11_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4068])).

fof(f4068,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_yellow_6(X0,X1) != k11_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4030])).

fof(f4030,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => k4_yellow_6(X0,X1) = k11_yellow_6(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4029])).

fof(f4029,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => k4_yellow_6(X0,X1) = k11_yellow_6(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_6)).

fof(f5117,plain,(
    l1_waybel_0(sK39,sK38) ),
    inference(cnf_transformation,[],[f4714])).

fof(f5109,plain,(
    ~ v2_struct_0(sK38) ),
    inference(cnf_transformation,[],[f4714])).

fof(f9269,plain,(
    ~ m1_subset_1(k4_yellow_6(sK38,sK39),u1_struct_0(sK38)) ),
    inference(unit_resulting_resolution,[],[f5109,f5110,f5111,f5112,f5113,f5114,f5115,f6058,f5117,f5118,f6057,f5121])).

fof(f5121,plain,(
    ! [X2,X0,X1] :
      ( k11_yellow_6(X0,X1) = X2
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4715])).

fof(f4715,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k11_yellow_6(X0,X1) = X2
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
                & ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | k11_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4073])).

fof(f4073,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4072])).

fof(f4072,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3833])).

fof(f3833,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_yellow_6)).

fof(f6057,plain,(
    r2_hidden(k4_yellow_6(sK38,sK39),k10_yellow_6(sK38,sK39)) ),
    inference(unit_resulting_resolution,[],[f5109,f5110,f5112,f5113,f5114,f5115,f5116,f5117,f5123])).

fof(f5123,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4077])).

fof(f4077,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4076])).

fof(f4076,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4026])).

fof(f4026,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_6)).

fof(f5116,plain,(
    v1_yellow_6(sK39,sK38) ),
    inference(cnf_transformation,[],[f4714])).

fof(f5118,plain,(
    k4_yellow_6(sK38,sK39) != k11_yellow_6(sK38,sK39) ),
    inference(cnf_transformation,[],[f4714])).

fof(f6058,plain,(
    v3_yellow_6(sK39,sK38) ),
    inference(unit_resulting_resolution,[],[f5109,f5110,f5112,f5115,f5113,f5114,f5116,f5117,f5171])).

fof(f5171,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4095])).

fof(f4095,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4094])).

fof(f4094,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3808])).

fof(f3808,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( ( v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_6)).

fof(f5115,plain,(
    v7_waybel_0(sK39) ),
    inference(cnf_transformation,[],[f4714])).

fof(f5114,plain,(
    v4_orders_2(sK39) ),
    inference(cnf_transformation,[],[f4714])).

fof(f5113,plain,(
    ~ v2_struct_0(sK39) ),
    inference(cnf_transformation,[],[f4714])).

fof(f5111,plain,(
    v8_pre_topc(sK38) ),
    inference(cnf_transformation,[],[f4714])).

fof(f5110,plain,(
    v2_pre_topc(sK38) ),
    inference(cnf_transformation,[],[f4714])).
%------------------------------------------------------------------------------
