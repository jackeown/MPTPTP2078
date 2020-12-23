%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2013+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Timeout 58.05s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  301 ( 719 expanded)
%              Number of leaves         :   64 ( 265 expanded)
%              Depth                    :   18
%              Number of atoms          : 1286 (2899 expanded)
%              Number of equality atoms :   94 ( 248 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5947,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4680,f4685,f4690,f4695,f4700,f4705,f4710,f4715,f4720,f4725,f4730,f4735,f4740,f4767,f4782,f4799,f4848,f4862,f4882,f4925,f4959,f5022,f5057,f5115,f5179,f5249,f5416,f5609,f5634,f5641,f5649,f5654,f5673,f5741,f5847,f5859,f5890,f5902,f5926,f5936,f5946])).

fof(f5946,plain,
    ( spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41
    | spl33_42
    | ~ spl33_45 ),
    inference(avatar_contradiction_clause,[],[f5945])).

fof(f5945,plain,
    ( $false
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41
    | spl33_42
    | ~ spl33_45 ),
    inference(subsumption_resolution,[],[f5944,f4684])).

fof(f4684,plain,
    ( ~ v2_struct_0(sK0)
    | spl33_2 ),
    inference(avatar_component_clause,[],[f4682])).

fof(f4682,plain,
    ( spl33_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_2])])).

fof(f5944,plain,
    ( v2_struct_0(sK0)
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41
    | spl33_42
    | ~ spl33_45 ),
    inference(subsumption_resolution,[],[f5943,f5901])).

fof(f5901,plain,
    ( r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | ~ spl33_45 ),
    inference(avatar_component_clause,[],[f5899])).

fof(f5899,plain,
    ( spl33_45
  <=> r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_45])])).

fof(f5943,plain,
    ( ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41
    | spl33_42 ),
    inference(subsumption_resolution,[],[f5942,f5881])).

fof(f5881,plain,
    ( m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(backward_demodulation,[],[f5869,f5879])).

fof(f5879,plain,
    ( sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5878,f4684])).

fof(f5878,plain,
    ( sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5877,f4699])).

fof(f4699,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl33_5 ),
    inference(avatar_component_clause,[],[f4697])).

fof(f4697,plain,
    ( spl33_5
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_5])])).

fof(f5877,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5876,f4694])).

fof(f4694,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl33_4 ),
    inference(avatar_component_clause,[],[f4692])).

fof(f4692,plain,
    ( spl33_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_4])])).

fof(f5876,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5875,f4679])).

fof(f4679,plain,
    ( ~ v2_struct_0(sK1)
    | spl33_1 ),
    inference(avatar_component_clause,[],[f4677])).

fof(f4677,plain,
    ( spl33_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_1])])).

fof(f5875,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl33_3
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5862,f4689])).

fof(f4689,plain,
    ( l1_struct_0(sK0)
    | ~ spl33_3 ),
    inference(avatar_component_clause,[],[f4687])).

fof(f4687,plain,
    ( spl33_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_3])])).

fof(f5862,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl33_41 ),
    inference(resolution,[],[f5841,f4673])).

fof(f4673,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK11(X1,X2,X4) = X4
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4672,f4525])).

fof(f4525,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4393])).

fof(f4393,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4392])).

fof(f4392,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4334])).

fof(f4334,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f4672,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | sK11(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f4662,f4524])).

fof(f4524,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4393])).

fof(f4662,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | sK11(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f4527])).

fof(f4527,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | sK11(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f4395])).

fof(f4395,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4394])).

fof(f4394,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4325])).

fof(f4325,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f5841,plain,
    ( r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl33_41 ),
    inference(avatar_component_clause,[],[f5840])).

fof(f5840,plain,
    ( spl33_41
  <=> r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_41])])).

fof(f5869,plain,
    ( m1_subset_1(sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5868,f4684])).

fof(f5868,plain,
    ( m1_subset_1(sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5867,f4699])).

fof(f5867,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5866,f4694])).

fof(f5866,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5865,f4679])).

fof(f5865,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl33_3
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5860,f4689])).

fof(f5860,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl33_41 ),
    inference(resolution,[],[f5841,f4675])).

fof(f4675,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(sK11(X1,X2,X4),u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4674,f4525])).

fof(f4674,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | m1_subset_1(sK11(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f4663,f4524])).

fof(f4663,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | m1_subset_1(sK11(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f4526])).

fof(f4526,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | m1_subset_1(sK11(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f4395])).

fof(f5942,plain,
    ( ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | spl33_42 ),
    inference(subsumption_resolution,[],[f5941,f4699])).

fof(f5941,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | spl33_42 ),
    inference(subsumption_resolution,[],[f5940,f4694])).

fof(f5940,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | spl33_42 ),
    inference(subsumption_resolution,[],[f5939,f4679])).

fof(f5939,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl33_3
    | spl33_42 ),
    inference(subsumption_resolution,[],[f5938,f4689])).

fof(f5938,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_42 ),
    inference(resolution,[],[f5846,f4655])).

fof(f4655,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_orders_2(X2,X3,X4)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f4523])).

fof(f4523,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | X0 != X4
      | ~ r1_orders_2(X2,X3,X4)
      | r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f4391])).

fof(f4391,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f4390])).

fof(f4390,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4357])).

fof(f4357,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(f5846,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | spl33_42 ),
    inference(avatar_component_clause,[],[f5844])).

fof(f5844,plain,
    ( spl33_42
  <=> r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_42])])).

fof(f5936,plain,
    ( spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | spl33_41
    | ~ spl33_42 ),
    inference(avatar_contradiction_clause,[],[f5935])).

fof(f5935,plain,
    ( $false
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | spl33_41
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5934,f4684])).

fof(f5934,plain,
    ( v2_struct_0(sK0)
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | spl33_41
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5933,f5924])).

fof(f5924,plain,
    ( r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42 ),
    inference(backward_demodulation,[],[f5912,f5922])).

fof(f5922,plain,
    ( sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5921,f4684])).

fof(f5921,plain,
    ( sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5920,f4699])).

fof(f5920,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5919,f4694])).

fof(f5919,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5918,f4679])).

fof(f5918,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl33_3
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5906,f4689])).

fof(f5906,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl33_42 ),
    inference(resolution,[],[f5845,f4521])).

fof(f4521,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | sK8(X0,X2,X3) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f4391])).

fof(f5845,plain,
    ( r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl33_42 ),
    inference(avatar_component_clause,[],[f5844])).

fof(f5912,plain,
    ( r1_orders_2(sK1,sK2,sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5911,f4684])).

fof(f5911,plain,
    ( r1_orders_2(sK1,sK2,sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5910,f4699])).

fof(f5910,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5909,f4694])).

fof(f5909,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5908,f4679])).

fof(f5908,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl33_3
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5904,f4689])).

fof(f5904,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl33_42 ),
    inference(resolution,[],[f5845,f4522])).

fof(f4522,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_orders_2(X2,X3,sK8(X0,X2,X3))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f4391])).

fof(f5933,plain,
    ( ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | spl33_41
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5932,f5923])).

fof(f5923,plain,
    ( m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42 ),
    inference(backward_demodulation,[],[f5917,f5922])).

fof(f5917,plain,
    ( m1_subset_1(sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5916,f4684])).

fof(f5916,plain,
    ( m1_subset_1(sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5915,f4699])).

fof(f5915,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5914,f4694])).

fof(f5914,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5913,f4679])).

fof(f5913,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl33_3
    | ~ spl33_42 ),
    inference(subsumption_resolution,[],[f5905,f4689])).

fof(f5905,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK8(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl33_42 ),
    inference(resolution,[],[f5845,f4520])).

fof(f4520,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | m1_subset_1(sK8(X0,X2,X3),u1_struct_0(X2))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f4391])).

fof(f5932,plain,
    ( ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | spl33_41 ),
    inference(subsumption_resolution,[],[f5931,f4699])).

fof(f5931,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | spl33_41 ),
    inference(subsumption_resolution,[],[f5930,f4694])).

fof(f5930,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | spl33_41 ),
    inference(subsumption_resolution,[],[f5929,f4679])).

fof(f5929,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl33_3
    | spl33_41 ),
    inference(subsumption_resolution,[],[f5928,f4689])).

fof(f5928,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl33_41 ),
    inference(resolution,[],[f5842,f4669])).

fof(f4669,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4668,f4525])).

fof(f4668,plain,(
    ! [X2,X0,X5,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f4660,f4524])).

fof(f4660,plain,(
    ! [X2,X0,X5,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f4659])).

fof(f4659,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f4529])).

fof(f4529,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X4 != X5
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f4395])).

fof(f5842,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | spl33_41 ),
    inference(avatar_component_clause,[],[f5840])).

fof(f5926,plain,
    ( spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42
    | spl33_45 ),
    inference(avatar_contradiction_clause,[],[f5925])).

fof(f5925,plain,
    ( $false
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_42
    | spl33_45 ),
    inference(subsumption_resolution,[],[f5924,f5900])).

fof(f5900,plain,
    ( ~ r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | spl33_45 ),
    inference(avatar_component_clause,[],[f5899])).

fof(f5902,plain,
    ( spl33_45
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(avatar_split_clause,[],[f5880,f5840,f4697,f4692,f4687,f4682,f4677,f5899])).

fof(f5880,plain,
    ( r1_orders_2(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(backward_demodulation,[],[f5874,f5879])).

fof(f5874,plain,
    ( r1_orders_2(sK1,sK2,sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5873,f4684])).

fof(f5873,plain,
    ( r1_orders_2(sK1,sK2,sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5872,f4699])).

fof(f5872,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5871,f4694])).

fof(f5871,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | spl33_1
    | ~ spl33_3
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5870,f4679])).

fof(f5870,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl33_3
    | ~ spl33_41 ),
    inference(subsumption_resolution,[],[f5861,f4689])).

fof(f5861,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK11(sK1,sK2,sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl33_41 ),
    inference(resolution,[],[f5841,f4671])).

fof(f4671,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_orders_2(X1,X2,sK11(X1,X2,X4))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4670,f4525])).

fof(f4670,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | r1_orders_2(X1,X2,sK11(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f4661,f4524])).

fof(f4661,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | r1_orders_2(X1,X2,sK11(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f4528])).

fof(f4528,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | r1_orders_2(X1,X2,sK11(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f4395])).

fof(f5890,plain,
    ( ~ spl33_43
    | ~ spl33_44
    | spl33_13 ),
    inference(avatar_split_clause,[],[f5029,f4737,f5887,f5883])).

fof(f5883,plain,
    ( spl33_43
  <=> r2_hidden(sK4(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_43])])).

fof(f5887,plain,
    ( spl33_44
  <=> r2_hidden(sK4(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_44])])).

fof(f4737,plain,
    ( spl33_13
  <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_13])])).

fof(f5029,plain,
    ( ~ r2_hidden(sK4(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ r2_hidden(sK4(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | spl33_13 ),
    inference(extensionality_resolution,[],[f4510,f4739])).

fof(f4739,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) != a_3_0_waybel_9(sK0,sK1,sK2)
    | spl33_13 ),
    inference(avatar_component_clause,[],[f4737])).

fof(f4510,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4382])).

fof(f4382,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f5859,plain,
    ( spl33_13
    | spl33_41
    | spl33_42 ),
    inference(avatar_contradiction_clause,[],[f5858])).

fof(f5858,plain,
    ( $false
    | spl33_13
    | spl33_41
    | spl33_42 ),
    inference(subsumption_resolution,[],[f5857,f4739])).

fof(f5857,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | spl33_41
    | spl33_42 ),
    inference(subsumption_resolution,[],[f5855,f5846])).

fof(f5855,plain,
    ( r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | spl33_41 ),
    inference(resolution,[],[f5842,f4509])).

fof(f4509,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4382])).

fof(f5847,plain,
    ( ~ spl33_41
    | ~ spl33_42
    | spl33_13 ),
    inference(avatar_split_clause,[],[f5028,f4737,f5844,f5840])).

fof(f5028,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ r2_hidden(sK4(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | spl33_13 ),
    inference(extensionality_resolution,[],[f4510,f4739])).

fof(f5741,plain,
    ( spl33_40
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5 ),
    inference(avatar_split_clause,[],[f5736,f4697,f4692,f4687,f4682,f4677,f5738])).

fof(f5738,plain,
    ( spl33_40
  <=> u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_40])])).

fof(f5736,plain,
    ( u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | spl33_1
    | spl33_2
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5 ),
    inference(subsumption_resolution,[],[f5735,f4684])).

fof(f5735,plain,
    ( v2_struct_0(sK0)
    | u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | spl33_1
    | ~ spl33_3
    | ~ spl33_4
    | ~ spl33_5 ),
    inference(subsumption_resolution,[],[f5734,f4689])).

fof(f5734,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | spl33_1
    | ~ spl33_4
    | ~ spl33_5 ),
    inference(resolution,[],[f5580,f4694])).

fof(f5580,plain,
    ( ! [X6] :
        ( ~ l1_waybel_0(sK1,X6)
        | ~ l1_struct_0(X6)
        | v2_struct_0(X6)
        | u1_waybel_0(X6,k4_waybel_9(X6,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X6),u1_waybel_0(X6,sK1),u1_struct_0(k4_waybel_9(X6,sK1,sK2))) )
    | spl33_1
    | ~ spl33_5 ),
    inference(subsumption_resolution,[],[f5569,f4679])).

fof(f5569,plain,
    ( ! [X6] :
        ( ~ l1_struct_0(X6)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,X6)
        | v2_struct_0(X6)
        | u1_waybel_0(X6,k4_waybel_9(X6,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X6),u1_waybel_0(X6,sK1),u1_struct_0(k4_waybel_9(X6,sK1,sK2))) )
    | ~ spl33_5 ),
    inference(resolution,[],[f4665,f4699])).

fof(f4665,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f4664,f4525])).

fof(f4664,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f4656,f4524])).

fof(f4656,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f4535])).

fof(f4535,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f4395])).

fof(f5673,plain,
    ( spl33_39
    | ~ spl33_12 ),
    inference(avatar_split_clause,[],[f4794,f4732,f5670])).

fof(f5670,plain,
    ( spl33_39
  <=> u1_struct_0(sK23) = k2_struct_0(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_39])])).

fof(f4732,plain,
    ( spl33_12
  <=> l1_struct_0(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_12])])).

fof(f4794,plain,
    ( u1_struct_0(sK23) = k2_struct_0(sK23)
    | ~ spl33_12 ),
    inference(resolution,[],[f4646,f4734])).

fof(f4734,plain,
    ( l1_struct_0(sK23)
    | ~ spl33_12 ),
    inference(avatar_component_clause,[],[f4732])).

fof(f4646,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4489])).

fof(f4489,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f5654,plain,
    ( spl33_38
    | ~ spl33_9 ),
    inference(avatar_split_clause,[],[f4793,f4717,f5651])).

fof(f5651,plain,
    ( spl33_38
  <=> u1_struct_0(sK22) = k2_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_38])])).

fof(f4717,plain,
    ( spl33_9
  <=> l1_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_9])])).

fof(f4793,plain,
    ( u1_struct_0(sK22) = k2_struct_0(sK22)
    | ~ spl33_9 ),
    inference(resolution,[],[f4646,f4719])).

fof(f4719,plain,
    ( l1_struct_0(sK22)
    | ~ spl33_9 ),
    inference(avatar_component_clause,[],[f4717])).

fof(f5649,plain,
    ( spl33_37
    | ~ spl33_6 ),
    inference(avatar_split_clause,[],[f4792,f4702,f5646])).

fof(f5646,plain,
    ( spl33_37
  <=> u1_struct_0(sK21) = k2_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_37])])).

fof(f4702,plain,
    ( spl33_6
  <=> l1_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_6])])).

fof(f4792,plain,
    ( u1_struct_0(sK21) = k2_struct_0(sK21)
    | ~ spl33_6 ),
    inference(resolution,[],[f4646,f4704])).

fof(f4704,plain,
    ( l1_struct_0(sK21)
    | ~ spl33_6 ),
    inference(avatar_component_clause,[],[f4702])).

fof(f5641,plain,
    ( spl33_36
    | ~ spl33_17
    | ~ spl33_21
    | ~ spl33_24 ),
    inference(avatar_split_clause,[],[f5301,f5054,f4922,f4796,f5638])).

fof(f5638,plain,
    ( spl33_36
  <=> u1_struct_0(sK1) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_36])])).

fof(f4796,plain,
    ( spl33_17
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_17])])).

fof(f4922,plain,
    ( spl33_21
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_21])])).

fof(f5054,plain,
    ( spl33_24
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_24])])).

fof(f5301,plain,
    ( u1_struct_0(sK1) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl33_17
    | ~ spl33_21
    | ~ spl33_24 ),
    inference(forward_demodulation,[],[f5300,f4924])).

fof(f4924,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl33_21 ),
    inference(avatar_component_clause,[],[f4922])).

fof(f5300,plain,
    ( k2_struct_0(sK1) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl33_17
    | ~ spl33_24 ),
    inference(subsumption_resolution,[],[f5278,f4798])).

fof(f4798,plain,
    ( l1_struct_0(sK1)
    | ~ spl33_17 ),
    inference(avatar_component_clause,[],[f4796])).

fof(f5278,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl33_24 ),
    inference(resolution,[],[f4633,f5056])).

fof(f5056,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl33_24 ),
    inference(avatar_component_clause,[],[f5054])).

fof(f4633,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f4478])).

fof(f4478,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1823])).

fof(f1823,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f5634,plain,
    ( ~ spl33_34
    | ~ spl33_35
    | spl33_13 ),
    inference(avatar_split_clause,[],[f4840,f4737,f5631,f5627])).

fof(f5627,plain,
    ( spl33_34
  <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_34])])).

fof(f5631,plain,
    ( spl33_35
  <=> r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_35])])).

fof(f4840,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | spl33_13 ),
    inference(extensionality_resolution,[],[f4508,f4739])).

fof(f4508,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5609,plain,
    ( spl33_33
    | ~ spl33_3
    | ~ spl33_19
    | ~ spl33_23 ),
    inference(avatar_split_clause,[],[f5299,f5019,f4859,f4687,f5606])).

fof(f5606,plain,
    ( spl33_33
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_33])])).

fof(f4859,plain,
    ( spl33_19
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_19])])).

fof(f5019,plain,
    ( spl33_23
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_23])])).

fof(f5299,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl33_3
    | ~ spl33_19
    | ~ spl33_23 ),
    inference(forward_demodulation,[],[f5298,f4861])).

fof(f4861,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl33_19 ),
    inference(avatar_component_clause,[],[f4859])).

fof(f5298,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl33_3
    | ~ spl33_23 ),
    inference(subsumption_resolution,[],[f5277,f4689])).

fof(f5277,plain,
    ( ~ l1_struct_0(sK0)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl33_23 ),
    inference(resolution,[],[f4633,f5021])).

fof(f5021,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl33_23 ),
    inference(avatar_component_clause,[],[f5019])).

fof(f5416,plain,
    ( spl33_31
    | spl33_32
    | ~ spl33_24 ),
    inference(avatar_split_clause,[],[f5074,f5054,f5413,f5409])).

fof(f5409,plain,
    ( spl33_31
  <=> r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_31])])).

fof(f5413,plain,
    ( spl33_32
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_32])])).

fof(f5074,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl33_24 ),
    inference(resolution,[],[f5056,f4550])).

fof(f4550,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4412])).

fof(f4412,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f4411])).

fof(f4411,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f5249,plain,
    ( spl33_29
    | spl33_30
    | ~ spl33_23 ),
    inference(avatar_split_clause,[],[f5045,f5019,f5246,f5242])).

fof(f5242,plain,
    ( spl33_29
  <=> r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_29])])).

fof(f5246,plain,
    ( spl33_30
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_30])])).

fof(f5045,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl33_23 ),
    inference(resolution,[],[f5021,f4550])).

fof(f5179,plain,
    ( ~ spl33_27
    | spl33_28
    | ~ spl33_5
    | ~ spl33_17 ),
    inference(avatar_split_clause,[],[f5107,f4796,f4697,f5177,f5173])).

fof(f5173,plain,
    ( spl33_27
  <=> v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_27])])).

fof(f5177,plain,
    ( spl33_28
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK1))
        | sK2 = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_28])])).

fof(f5107,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK1))
        | sK2 = X6
        | ~ v7_struct_0(sK1) )
    | ~ spl33_5
    | ~ spl33_17 ),
    inference(subsumption_resolution,[],[f5098,f4798])).

fof(f5098,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | sK2 = X6
        | ~ v7_struct_0(sK1) )
    | ~ spl33_5 ),
    inference(resolution,[],[f4641,f4699])).

fof(f4641,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | X1 = X2
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4483])).

fof(f4483,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4117])).

fof(f4117,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v7_struct_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_struct_0)).

fof(f5115,plain,
    ( ~ spl33_25
    | spl33_26
    | ~ spl33_23 ),
    inference(avatar_split_clause,[],[f5038,f5019,f5113,f5109])).

fof(f5109,plain,
    ( spl33_25
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_25])])).

fof(f5113,plain,
    ( spl33_26
  <=> ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_26])])).

fof(f5038,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl33_23 ),
    inference(resolution,[],[f5021,f4538])).

fof(f4538,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f4400])).

fof(f4400,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f629])).

fof(f629,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f5057,plain,
    ( spl33_24
    | ~ spl33_17
    | ~ spl33_21 ),
    inference(avatar_split_clause,[],[f4953,f4922,f4796,f5054])).

fof(f4953,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl33_17
    | ~ spl33_21 ),
    inference(subsumption_resolution,[],[f4949,f4798])).

fof(f4949,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(sK1)
    | ~ spl33_21 ),
    inference(superposition,[],[f4645,f4924])).

fof(f4645,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4488])).

fof(f4488,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1781])).

fof(f1781,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f5022,plain,
    ( spl33_23
    | ~ spl33_3
    | ~ spl33_19 ),
    inference(avatar_split_clause,[],[f4869,f4859,f4687,f5019])).

fof(f4869,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl33_3
    | ~ spl33_19 ),
    inference(subsumption_resolution,[],[f4865,f4689])).

fof(f4865,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl33_19 ),
    inference(superposition,[],[f4645,f4861])).

fof(f4959,plain,
    ( ~ spl33_22
    | ~ spl33_17
    | ~ spl33_21 ),
    inference(avatar_split_clause,[],[f4954,f4922,f4796,f4956])).

fof(f4956,plain,
    ( spl33_22
  <=> v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_22])])).

fof(f4954,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl33_17
    | ~ spl33_21 ),
    inference(subsumption_resolution,[],[f4950,f4798])).

fof(f4950,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ spl33_21 ),
    inference(superposition,[],[f4647,f4924])).

fof(f4647,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4490])).

fof(f4490,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1791])).

fof(f1791,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f4925,plain,
    ( spl33_21
    | ~ spl33_17 ),
    inference(avatar_split_clause,[],[f4807,f4796,f4922])).

fof(f4807,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl33_17 ),
    inference(resolution,[],[f4798,f4646])).

fof(f4882,plain,
    ( ~ spl33_20
    | ~ spl33_3
    | ~ spl33_19 ),
    inference(avatar_split_clause,[],[f4870,f4859,f4687,f4879])).

fof(f4879,plain,
    ( spl33_20
  <=> v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_20])])).

fof(f4870,plain,
    ( ~ v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl33_3
    | ~ spl33_19 ),
    inference(subsumption_resolution,[],[f4866,f4689])).

fof(f4866,plain,
    ( ~ v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl33_19 ),
    inference(superposition,[],[f4647,f4861])).

fof(f4862,plain,
    ( spl33_19
    | ~ spl33_3 ),
    inference(avatar_split_clause,[],[f4791,f4687,f4859])).

fof(f4791,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl33_3 ),
    inference(resolution,[],[f4646,f4689])).

fof(f4848,plain,
    ( spl33_18
    | ~ spl33_5
    | spl33_14 ),
    inference(avatar_split_clause,[],[f4815,f4760,f4697,f4845])).

fof(f4845,plain,
    ( spl33_18
  <=> r2_hidden(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_18])])).

fof(f4760,plain,
    ( spl33_14
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_14])])).

fof(f4815,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl33_5
    | spl33_14 ),
    inference(subsumption_resolution,[],[f4811,f4762])).

fof(f4762,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl33_14 ),
    inference(avatar_component_clause,[],[f4760])).

fof(f4811,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl33_5 ),
    inference(resolution,[],[f4550,f4699])).

fof(f4799,plain,
    ( spl33_17
    | ~ spl33_16 ),
    inference(avatar_split_clause,[],[f4787,f4779,f4796])).

fof(f4779,plain,
    ( spl33_16
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_16])])).

fof(f4787,plain,
    ( l1_struct_0(sK1)
    | ~ spl33_16 ),
    inference(resolution,[],[f4781,f4630])).

fof(f4630,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4474])).

fof(f4474,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f4781,plain,
    ( l1_orders_2(sK1)
    | ~ spl33_16 ),
    inference(avatar_component_clause,[],[f4779])).

fof(f4782,plain,
    ( spl33_16
    | ~ spl33_3
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f4775,f4692,f4687,f4779])).

fof(f4775,plain,
    ( l1_orders_2(sK1)
    | ~ spl33_3
    | ~ spl33_4 ),
    inference(subsumption_resolution,[],[f4768,f4689])).

fof(f4768,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1)
    | ~ spl33_4 ),
    inference(resolution,[],[f4585,f4694])).

fof(f4585,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f4432])).

fof(f4432,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3197])).

fof(f3197,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f4767,plain,
    ( ~ spl33_14
    | spl33_15
    | ~ spl33_5 ),
    inference(avatar_split_clause,[],[f4752,f4697,f4764,f4760])).

fof(f4764,plain,
    ( spl33_15
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_15])])).

fof(f4752,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl33_5 ),
    inference(resolution,[],[f4555,f4699])).

fof(f4555,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f4416])).

fof(f4416,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f4740,plain,(
    ~ spl33_13 ),
    inference(avatar_split_clause,[],[f4496,f4737])).

fof(f4496,plain,(
    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) != a_3_0_waybel_9(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f4380])).

fof(f4380,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4379])).

fof(f4379,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4365])).

fof(f4365,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4364])).

fof(f4364,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

fof(f4735,plain,(
    spl33_12 ),
    inference(avatar_split_clause,[],[f4592,f4732])).

fof(f4592,plain,(
    l1_struct_0(sK23) ),
    inference(cnf_transformation,[],[f1789])).

fof(f1789,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_struct_0)).

fof(f4730,plain,(
    ~ spl33_11 ),
    inference(avatar_split_clause,[],[f4591,f4727])).

fof(f4727,plain,
    ( spl33_11
  <=> v7_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_11])])).

fof(f4591,plain,(
    ~ v7_struct_0(sK22) ),
    inference(cnf_transformation,[],[f1811])).

fof(f1811,axiom,(
    ? [X0] :
      ( ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc10_struct_0)).

fof(f4725,plain,(
    ~ spl33_10 ),
    inference(avatar_split_clause,[],[f4590,f4722])).

fof(f4722,plain,
    ( spl33_10
  <=> v2_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_10])])).

fof(f4590,plain,(
    ~ v2_struct_0(sK22) ),
    inference(cnf_transformation,[],[f1811])).

fof(f4720,plain,(
    spl33_9 ),
    inference(avatar_split_clause,[],[f4589,f4717])).

fof(f4589,plain,(
    l1_struct_0(sK22) ),
    inference(cnf_transformation,[],[f1811])).

fof(f4715,plain,(
    spl33_8 ),
    inference(avatar_split_clause,[],[f4588,f4712])).

fof(f4712,plain,
    ( spl33_8
  <=> v7_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_8])])).

fof(f4588,plain,(
    v7_struct_0(sK21) ),
    inference(cnf_transformation,[],[f1820])).

fof(f1820,axiom,(
    ? [X0] :
      ( v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc9_struct_0)).

fof(f4710,plain,(
    ~ spl33_7 ),
    inference(avatar_split_clause,[],[f4587,f4707])).

fof(f4707,plain,
    ( spl33_7
  <=> v2_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_7])])).

fof(f4587,plain,(
    ~ v2_struct_0(sK21) ),
    inference(cnf_transformation,[],[f1820])).

fof(f4705,plain,(
    spl33_6 ),
    inference(avatar_split_clause,[],[f4586,f4702])).

fof(f4586,plain,(
    l1_struct_0(sK21) ),
    inference(cnf_transformation,[],[f1820])).

fof(f4700,plain,(
    spl33_5 ),
    inference(avatar_split_clause,[],[f4495,f4697])).

fof(f4495,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f4380])).

fof(f4695,plain,(
    spl33_4 ),
    inference(avatar_split_clause,[],[f4498,f4692])).

fof(f4498,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f4380])).

fof(f4690,plain,(
    spl33_3 ),
    inference(avatar_split_clause,[],[f4500,f4687])).

fof(f4500,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f4380])).

fof(f4685,plain,(
    ~ spl33_2 ),
    inference(avatar_split_clause,[],[f4499,f4682])).

fof(f4499,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f4380])).

fof(f4680,plain,(
    ~ spl33_1 ),
    inference(avatar_split_clause,[],[f4497,f4677])).

fof(f4497,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f4380])).
%------------------------------------------------------------------------------
