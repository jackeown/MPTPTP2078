%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1975+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:59 EST 2020

% Result     : Theorem 7.40s
% Output     : Refutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :  745 (5261 expanded)
%              Number of leaves         :  184 (2406 expanded)
%              Depth                    :   17
%              Number of atoms          : 3689 (19139 expanded)
%              Number of equality atoms :  178 (1367 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5834,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f175,f180,f186,f191,f203,f213,f220,f229,f245,f269,f293,f303,f312,f317,f322,f354,f368,f385,f394,f399,f404,f413,f418,f424,f489,f497,f554,f598,f720,f725,f730,f736,f741,f851,f889,f898,f908,f915,f920,f925,f1085,f1129,f1168,f1320,f1347,f1354,f1359,f1364,f1369,f1374,f1639,f1850,f1857,f1862,f1867,f1872,f1877,f2227,f2476,f2482,f2490,f2500,f2509,f2755,f2760,f2765,f2770,f2775,f2780,f2785,f2790,f2795,f2800,f2806,f2813,f2818,f2823,f2862,f2867,f2872,f2877,f2882,f2887,f3174,f3180,f3185,f3197,f3202,f3207,f3212,f3217,f3222,f3227,f3253,f3258,f3263,f3268,f3273,f3278,f3283,f3393,f3449,f3493,f3592,f3597,f3602,f3645,f3650,f3655,f3660,f3665,f3670,f3676,f3681,f3686,f3691,f3697,f3702,f3707,f3712,f3738,f3742,f3747,f3779,f3793,f3800,f3921,f3926,f3931,f3946,f3961,f3966,f3971,f3976,f4207,f4212,f4217,f4222,f4227,f4232,f4237,f4242,f4247,f5235,f5240,f5245,f5250,f5258,f5263,f5269,f5274,f5284,f5404,f5409,f5414,f5419,f5424,f5812,f5821,f5830])).

fof(f5830,plain,
    ( ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | spl10_105
    | ~ spl10_163 ),
    inference(avatar_contradiction_clause,[],[f5829])).

fof(f5829,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | spl10_105
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f5828,f3272])).

fof(f3272,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl10_105 ),
    inference(avatar_component_clause,[],[f3270])).

fof(f3270,plain,
    ( spl10_105
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f5828,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | ~ spl10_163 ),
    inference(forward_demodulation,[],[f5738,f2572])).

fof(f2572,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_70 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f2508,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) = k3_yellow_0(X0)
      | ~ v11_waybel_1(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_yellow_0(X0) = k13_lattice3(X0,X1,k7_waybel_1(X0,X1))
            & k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) = k3_yellow_0(X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_yellow_0(X0) = k13_lattice3(X0,X1,k7_waybel_1(X0,X1))
            & k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) = k3_yellow_0(X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k4_yellow_0(X0) = k13_lattice3(X0,X1,k7_waybel_1(X0,X1))
            & k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) = k3_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow_5)).

fof(f2508,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f2506])).

fof(f2506,plain,
    ( spl10_70
  <=> m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f150,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl10_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f135,plain,
    ( v11_waybel_1(sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl10_5
  <=> v11_waybel_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f185,plain,
    ( ~ v2_struct_0(sK0)
    | spl10_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl10_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f5738,plain,
    ( m1_subset_1(k12_lattice3(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_38
    | ~ spl10_163 ),
    inference(unit_resulting_resolution,[],[f496,f5413,f2729])).

fof(f2729,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | m1_subset_1(k12_lattice3(sK0,X1,X0),sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(resolution,[],[f687,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f687,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f686,f155])).

fof(f155,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl10_9
  <=> v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f686,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | ~ v2_waybel_0(sK1,sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f681,f165])).

fof(f165,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl10_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f681,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | ~ v2_waybel_0(sK1,sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(resolution,[],[f281,f160])).

fof(f160,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl10_10
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f281,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(k12_lattice3(sK0,X1,X2),X0)
        | ~ v2_waybel_0(X0,sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f280,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f280,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(k12_lattice3(sK0,X1,X2),X0)
        | ~ v2_waybel_0(X0,sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f279,f111])).

fof(f279,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(k12_lattice3(sK0,X1,X2),X0)
        | ~ v2_waybel_0(X0,sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f278,f130])).

fof(f130,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl10_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f278,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(k12_lattice3(sK0,X1,X2),X0)
        | ~ v2_waybel_0(X0,sK0) )
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f277,f145])).

fof(f145,plain,
    ( v2_lattice3(sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl10_7
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f277,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(k12_lattice3(sK0,X1,X2),X0)
        | ~ v2_waybel_0(X0,sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f103,f150])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k12_lattice3(X0,X2,X3),X1)
      | ~ v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_waybel_0)).

fof(f5413,plain,
    ( r2_hidden(k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),sK1)
    | ~ spl10_163 ),
    inference(avatar_component_clause,[],[f5411])).

fof(f5411,plain,
    ( spl10_163
  <=> r2_hidden(k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_163])])).

fof(f496,plain,
    ( r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl10_38
  <=> r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f5821,plain,
    ( ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | spl10_96
    | ~ spl10_163 ),
    inference(avatar_contradiction_clause,[],[f5820])).

fof(f5820,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | spl10_96
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f5819,f3206])).

fof(f3206,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl10_96 ),
    inference(avatar_component_clause,[],[f3204])).

fof(f3204,plain,
    ( spl10_96
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f5819,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | ~ spl10_163 ),
    inference(forward_demodulation,[],[f5764,f2572])).

fof(f5764,plain,
    ( r2_hidden(k12_lattice3(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_38
    | ~ spl10_163 ),
    inference(unit_resulting_resolution,[],[f496,f5413,f687])).

fof(f5812,plain,
    ( ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | spl10_96
    | ~ spl10_163 ),
    inference(avatar_contradiction_clause,[],[f5811])).

fof(f5811,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | spl10_96
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f5810,f3206])).

fof(f5810,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_38
    | ~ spl10_70
    | ~ spl10_163 ),
    inference(forward_demodulation,[],[f5797,f2572])).

fof(f5797,plain,
    ( r2_hidden(k12_lattice3(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_38
    | ~ spl10_163 ),
    inference(unit_resulting_resolution,[],[f496,f155,f160,f165,f5413,f281])).

fof(f5424,plain,
    ( spl10_165
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_63 ),
    inference(avatar_split_clause,[],[f2467,f1874,f300,f163,f158,f153,f148,f143,f128,f5421])).

fof(f5421,plain,
    ( spl10_165
  <=> r2_hidden(k12_lattice3(sK0,sK9(sK1),k12_lattice3(sK0,sK9(sK1),sK9(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_165])])).

fof(f300,plain,
    ( spl10_24
  <=> r2_hidden(sK9(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f1874,plain,
    ( spl10_63
  <=> r2_hidden(k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f2467,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK1),k12_lattice3(sK0,sK9(sK1),sK9(sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f302,f155,f160,f165,f1876,f281])).

fof(f1876,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK1)
    | ~ spl10_63 ),
    inference(avatar_component_clause,[],[f1874])).

fof(f302,plain,
    ( r2_hidden(sK9(sK1),sK1)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f300])).

fof(f5419,plain,
    ( ~ spl10_164
    | spl10_1
    | spl10_160 ),
    inference(avatar_split_clause,[],[f5385,f5281,f113,f5416])).

fof(f5416,plain,
    ( spl10_164
  <=> m1_subset_1(k7_waybel_1(sK0,sK9(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_164])])).

fof(f113,plain,
    ( spl10_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f5281,plain,
    ( spl10_160
  <=> r2_hidden(k7_waybel_1(sK0,sK9(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_160])])).

fof(f5385,plain,
    ( ~ m1_subset_1(k7_waybel_1(sK0,sK9(sK1)),sK1)
    | spl10_1
    | spl10_160 ),
    inference(unit_resulting_resolution,[],[f115,f5283,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f5283,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK9(sK1)),sK1)
    | spl10_160 ),
    inference(avatar_component_clause,[],[f5281])).

fof(f115,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f5414,plain,
    ( spl10_163
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_50
    | ~ spl10_51 ),
    inference(avatar_split_clause,[],[f1843,f1344,f922,f415,f410,f183,f163,f158,f153,f148,f143,f133,f128,f5411])).

fof(f410,plain,
    ( spl10_34
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f415,plain,
    ( spl10_35
  <=> m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f922,plain,
    ( spl10_50
  <=> r2_hidden(k7_waybel_1(sK0,sK5(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f1344,plain,
    ( spl10_51
  <=> r2_hidden(k7_waybel_1(sK0,sK6(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f1843,plain,
    ( r2_hidden(k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_50
    | ~ spl10_51 ),
    inference(forward_demodulation,[],[f1838,f456])).

fof(f456,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f412,f417,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_waybel_1(X0,k12_lattice3(X0,X1,X2)) = k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_waybel_1(X0,k12_lattice3(X0,X1,X2)) = k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k7_waybel_1(X0,k12_lattice3(X0,X1,X2)) = k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_5)).

fof(f417,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f415])).

fof(f412,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f410])).

fof(f1838,plain,
    ( r2_hidden(k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_50
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f924,f155,f160,f165,f1346,f281])).

fof(f1346,plain,
    ( r2_hidden(k7_waybel_1(sK0,sK6(sK0,sK1)),sK1)
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f924,plain,
    ( r2_hidden(k7_waybel_1(sK0,sK5(sK0,sK1)),sK1)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f922])).

fof(f5409,plain,
    ( spl10_162
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_35
    | ~ spl10_51 ),
    inference(avatar_split_clause,[],[f1842,f1344,f415,f183,f163,f158,f153,f148,f143,f133,f128,f5406])).

fof(f5406,plain,
    ( spl10_162
  <=> r2_hidden(k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK6(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).

fof(f1842,plain,
    ( r2_hidden(k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK6(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_35
    | ~ spl10_51 ),
    inference(forward_demodulation,[],[f1839,f461])).

fof(f461,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f417,f417,f89])).

fof(f1839,plain,
    ( r2_hidden(k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f1346,f155,f160,f165,f1346,f281])).

fof(f5404,plain,
    ( spl10_161
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_34
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f1824,f922,f410,f183,f163,f158,f153,f148,f143,f133,f128,f5401])).

fof(f5401,plain,
    ( spl10_161
  <=> r2_hidden(k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK5(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_161])])).

fof(f1824,plain,
    ( r2_hidden(k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK5(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_34
    | ~ spl10_50 ),
    inference(forward_demodulation,[],[f1821,f433])).

fof(f433,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK5(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f412,f412,f89])).

fof(f1821,plain,
    ( r2_hidden(k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f924,f155,f160,f165,f924,f281])).

fof(f5284,plain,
    ( ~ spl10_160
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | spl10_96
    | ~ spl10_152 ),
    inference(avatar_split_clause,[],[f5279,f5232,f3204,f300,f163,f158,f153,f148,f143,f128,f5281])).

fof(f5232,plain,
    ( spl10_152
  <=> k3_yellow_0(sK0) = k12_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK9(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_152])])).

fof(f5279,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK9(sK1)),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | spl10_96
    | ~ spl10_152 ),
    inference(subsumption_resolution,[],[f5278,f302])).

fof(f5278,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK9(sK1)),sK1)
    | ~ r2_hidden(sK9(sK1),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_96
    | ~ spl10_152 ),
    inference(subsumption_resolution,[],[f5277,f3206])).

fof(f5277,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k7_waybel_1(sK0,sK9(sK1)),sK1)
    | ~ r2_hidden(sK9(sK1),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_152 ),
    inference(superposition,[],[f687,f5234])).

fof(f5234,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK9(sK1)))
    | ~ spl10_152 ),
    inference(avatar_component_clause,[],[f5232])).

fof(f5274,plain,
    ( ~ spl10_159
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | ~ spl10_35
    | ~ spl10_63 ),
    inference(avatar_split_clause,[],[f2455,f1874,f415,f391,f163,f158,f148,f5271])).

fof(f5271,plain,
    ( spl10_159
  <=> r1_orders_2(sK0,k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_159])])).

fof(f391,plain,
    ( spl10_31
  <=> r2_hidden(sK6(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f2455,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK6(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | ~ spl10_35
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f160,f393,f417,f165,f1876,f247])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,X0)
        | ~ v13_waybel_0(X0,sK0) )
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f246,f111])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | ~ r1_orders_2(sK0,X1,X2)
        | r2_hidden(X2,X0)
        | ~ v13_waybel_0(X0,sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f85,f150])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f393,plain,
    ( ~ r2_hidden(sK6(sK0,sK1),sK1)
    | spl10_31 ),
    inference(avatar_component_clause,[],[f391])).

fof(f5269,plain,
    ( ~ spl10_158
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_32
    | ~ spl10_34
    | ~ spl10_63 ),
    inference(avatar_split_clause,[],[f2454,f1874,f410,f396,f163,f158,f148,f5266])).

fof(f5266,plain,
    ( spl10_158
  <=> r1_orders_2(sK0,k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_158])])).

fof(f396,plain,
    ( spl10_32
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f2454,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK5(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_32
    | ~ spl10_34
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f160,f398,f412,f165,f1876,f247])).

fof(f398,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl10_32 ),
    inference(avatar_component_clause,[],[f396])).

fof(f5263,plain,
    ( spl10_157
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_51 ),
    inference(avatar_split_clause,[],[f1840,f1344,f300,f163,f158,f153,f148,f143,f128,f5260])).

fof(f5260,plain,
    ( spl10_157
  <=> r2_hidden(k12_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK6(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_157])])).

fof(f1840,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK6(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f302,f155,f160,f165,f1346,f281])).

fof(f5258,plain,
    ( spl10_156
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f1822,f922,f300,f163,f158,f153,f148,f143,f128,f5255])).

fof(f5255,plain,
    ( spl10_156
  <=> r2_hidden(k12_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK5(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_156])])).

fof(f1822,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK5(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f302,f155,f160,f165,f924,f281])).

fof(f5250,plain,
    ( ~ spl10_155
    | spl10_138
    | spl10_49 ),
    inference(avatar_split_clause,[],[f1808,f917,f3943,f5247])).

fof(f5247,plain,
    ( spl10_155
  <=> m1_subset_1(k7_waybel_1(sK0,sK2),sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_155])])).

fof(f3943,plain,
    ( spl10_138
  <=> v1_xboole_0(sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_138])])).

fof(f917,plain,
    ( spl10_49
  <=> r2_hidden(k7_waybel_1(sK0,sK2),sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f1808,plain,
    ( v1_xboole_0(sK9(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(k7_waybel_1(sK0,sK2),sK9(k1_zfmisc_1(sK1)))
    | spl10_49 ),
    inference(resolution,[],[f919,f107])).

fof(f919,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK2),sK9(k1_zfmisc_1(sK1)))
    | spl10_49 ),
    inference(avatar_component_clause,[],[f917])).

fof(f5245,plain,
    ( spl10_154
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f3002,f2757,f266,f183,f148,f128,f5242])).

fof(f5242,plain,
    ( spl10_154
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f266,plain,
    ( spl10_22
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f2757,plain,
    ( spl10_72
  <=> m1_subset_1(k7_waybel_1(sK0,sK9(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f3002,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(sK1)))
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_72 ),
    inference(unit_resulting_resolution,[],[f185,f130,f150,f268,f2759,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f2759,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK9(sK1)),u1_struct_0(sK0))
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f2757])).

fof(f268,plain,
    ( v1_yellow_0(sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f266])).

fof(f5240,plain,
    ( spl10_153
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f782,f717,f183,f148,f133,f5237])).

fof(f5237,plain,
    ( spl10_153
  <=> k4_yellow_0(sK0) = k13_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK9(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_153])])).

fof(f717,plain,
    ( spl10_40
  <=> m1_subset_1(sK9(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f782,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK9(sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f719,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k4_yellow_0(X0) = k13_lattice3(X0,X1,k7_waybel_1(X0,X1))
      | ~ v11_waybel_1(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f719,plain,
    ( m1_subset_1(sK9(sK1),u1_struct_0(sK0))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f717])).

fof(f5235,plain,
    ( spl10_152
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f781,f717,f183,f148,f133,f5232])).

fof(f781,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,sK9(sK1),k7_waybel_1(sK0,sK9(sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f719,f87])).

fof(f4247,plain,
    ( spl10_151
    | ~ spl10_8
    | spl10_15
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f2331,f1869,f183,f148,f4244])).

fof(f4244,plain,
    ( spl10_151
  <=> m1_subset_1(k7_waybel_1(sK0,k7_waybel_1(sK0,sK6(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_151])])).

fof(f1869,plain,
    ( spl10_62
  <=> m1_subset_1(k7_waybel_1(sK0,sK6(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f2331,plain,
    ( m1_subset_1(k7_waybel_1(sK0,k7_waybel_1(sK0,sK6(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl10_8
    | spl10_15
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f185,f150,f1871,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_waybel_1)).

fof(f1871,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f1869])).

fof(f4242,plain,
    ( spl10_150
    | ~ spl10_8
    | spl10_15
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f2122,f1859,f183,f148,f4239])).

fof(f4239,plain,
    ( spl10_150
  <=> m1_subset_1(k7_waybel_1(sK0,k7_waybel_1(sK0,sK5(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_150])])).

fof(f1859,plain,
    ( spl10_60
  <=> m1_subset_1(k7_waybel_1(sK0,sK5(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f2122,plain,
    ( m1_subset_1(k7_waybel_1(sK0,k7_waybel_1(sK0,sK5(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl10_8
    | spl10_15
    | ~ spl10_60 ),
    inference(unit_resulting_resolution,[],[f185,f150,f1861,f108])).

fof(f1861,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f1859])).

fof(f4237,plain,
    ( ~ spl10_149
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_26
    | spl10_31
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f589,f415,f391,f314,f163,f158,f148,f4234])).

fof(f4234,plain,
    ( spl10_149
  <=> r1_orders_2(sK0,k4_yellow_0(sK0),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_149])])).

fof(f314,plain,
    ( spl10_26
  <=> r2_hidden(k4_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f589,plain,
    ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_26
    | spl10_31
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f316,f160,f393,f417,f165,f247])).

fof(f316,plain,
    ( r2_hidden(k4_yellow_0(sK0),sK1)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f314])).

fof(f4232,plain,
    ( spl10_148
    | ~ spl10_8
    | spl10_15
    | ~ spl10_59 ),
    inference(avatar_split_clause,[],[f1951,f1854,f183,f148,f4229])).

fof(f4229,plain,
    ( spl10_148
  <=> m1_subset_1(k7_waybel_1(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_148])])).

fof(f1854,plain,
    ( spl10_59
  <=> m1_subset_1(k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f1951,plain,
    ( m1_subset_1(k7_waybel_1(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl10_8
    | spl10_15
    | ~ spl10_59 ),
    inference(unit_resulting_resolution,[],[f185,f150,f1856,f108])).

fof(f1856,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f1854])).

fof(f4227,plain,
    ( ~ spl10_147
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | ~ spl10_35
    | ~ spl10_51 ),
    inference(avatar_split_clause,[],[f1830,f1344,f415,f391,f163,f158,f148,f4224])).

fof(f4224,plain,
    ( spl10_147
  <=> r1_orders_2(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_147])])).

fof(f1830,plain,
    ( ~ r1_orders_2(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),sK6(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | ~ spl10_35
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f160,f393,f417,f165,f1346,f247])).

fof(f4222,plain,
    ( ~ spl10_146
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_32
    | ~ spl10_34
    | ~ spl10_51 ),
    inference(avatar_split_clause,[],[f1829,f1344,f410,f396,f163,f158,f148,f4219])).

fof(f4219,plain,
    ( spl10_146
  <=> r1_orders_2(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_146])])).

fof(f1829,plain,
    ( ~ r1_orders_2(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),sK5(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_32
    | ~ spl10_34
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f160,f398,f412,f165,f1346,f247])).

fof(f4217,plain,
    ( ~ spl10_145
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | ~ spl10_35
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f1814,f922,f415,f391,f163,f158,f148,f4214])).

fof(f4214,plain,
    ( spl10_145
  <=> r1_orders_2(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_145])])).

fof(f1814,plain,
    ( ~ r1_orders_2(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),sK6(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | ~ spl10_35
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f160,f393,f417,f165,f924,f247])).

fof(f4212,plain,
    ( ~ spl10_144
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_26
    | spl10_32
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f587,f410,f396,f314,f163,f158,f148,f4209])).

fof(f4209,plain,
    ( spl10_144
  <=> r1_orders_2(sK0,k4_yellow_0(sK0),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_144])])).

fof(f587,plain,
    ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_26
    | spl10_32
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f316,f160,f398,f412,f165,f247])).

fof(f4207,plain,
    ( ~ spl10_143
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_32
    | ~ spl10_34
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f1813,f922,f410,f396,f163,f158,f148,f4204])).

fof(f4204,plain,
    ( spl10_143
  <=> r1_orders_2(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_143])])).

fof(f1813,plain,
    ( ~ r1_orders_2(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),sK5(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_32
    | ~ spl10_34
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f160,f398,f412,f165,f924,f247])).

fof(f3976,plain,
    ( spl10_142
    | ~ spl10_11
    | ~ spl10_63 ),
    inference(avatar_split_clause,[],[f2453,f1874,f163,f3973])).

fof(f3973,plain,
    ( spl10_142
  <=> m1_subset_1(k12_lattice3(sK0,sK9(sK1),sK9(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_142])])).

fof(f2453,plain,
    ( m1_subset_1(k12_lattice3(sK0,sK9(sK1),sK9(sK1)),u1_struct_0(sK0))
    | ~ spl10_11
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f165,f1876,f111])).

fof(f3971,plain,
    ( spl10_141
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1523,f912,f309,f183,f148,f133,f3968])).

fof(f3968,plain,
    ( spl10_141
  <=> k4_yellow_0(sK0) = k13_lattice3(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_141])])).

fof(f309,plain,
    ( spl10_25
  <=> m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f912,plain,
    ( spl10_48
  <=> m1_subset_1(k7_waybel_1(sK0,k4_yellow_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f1523,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f1490,f1465])).

fof(f1465,plain,
    ( k4_yellow_0(sK0) = k7_waybel_1(sK0,k3_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f1461,f1412])).

fof(f1412,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_48 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f914,f88])).

fof(f914,plain,
    ( m1_subset_1(k7_waybel_1(sK0,k4_yellow_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f912])).

fof(f1461,plain,
    ( k7_waybel_1(sK0,k3_yellow_0(sK0)) = k13_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f1425,f323])).

fof(f323,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,k4_yellow_0(sK0),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f311,f87])).

fof(f311,plain,
    ( m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f309])).

fof(f1425,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),k7_waybel_1(sK0,k4_yellow_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f311,f914,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_waybel_1(X0,k12_lattice3(X0,X1,X2)) = k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1490,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,k3_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f1412,f1467])).

fof(f1467,plain,
    ( k3_yellow_0(sK0) = k7_waybel_1(sK0,k4_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f1464,f1411])).

fof(f1411,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_48 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f914,f87])).

fof(f1464,plain,
    ( k7_waybel_1(sK0,k4_yellow_0(sK0)) = k12_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f1413,f324])).

fof(f324,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,k4_yellow_0(sK0),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f311,f88])).

fof(f1413,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),k7_waybel_1(sK0,k4_yellow_0(sK0)))) = k12_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f311,f914,f89])).

fof(f3966,plain,
    ( spl10_140
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1522,f912,f309,f183,f148,f133,f3963])).

fof(f3963,plain,
    ( spl10_140
  <=> k3_yellow_0(sK0) = k12_lattice3(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f1522,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f1489,f1465])).

fof(f1489,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,k3_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f1411,f1467])).

fof(f3961,plain,
    ( ~ spl10_139
    | spl10_137 ),
    inference(avatar_split_clause,[],[f3947,f3939,f3958])).

fof(f3958,plain,
    ( spl10_139
  <=> r2_hidden(sK2,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_139])])).

fof(f3939,plain,
    ( spl10_137
  <=> m1_subset_1(sK2,sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_137])])).

fof(f3947,plain,
    ( ~ r2_hidden(sK2,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK1)))))
    | spl10_137 ),
    inference(unit_resulting_resolution,[],[f105,f3941,f111])).

fof(f3941,plain,
    ( ~ m1_subset_1(sK2,sK9(k1_zfmisc_1(sK1)))
    | spl10_137 ),
    inference(avatar_component_clause,[],[f3939])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f3946,plain,
    ( ~ spl10_137
    | spl10_138
    | spl10_37 ),
    inference(avatar_split_clause,[],[f731,f486,f3943,f3939])).

fof(f486,plain,
    ( spl10_37
  <=> r2_hidden(sK2,sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f731,plain,
    ( v1_xboole_0(sK9(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,sK9(k1_zfmisc_1(sK1)))
    | spl10_37 ),
    inference(resolution,[],[f488,f107])).

fof(f488,plain,
    ( ~ r2_hidden(sK2,sK9(k1_zfmisc_1(sK1)))
    | spl10_37 ),
    inference(avatar_component_clause,[],[f486])).

fof(f3931,plain,
    ( ~ spl10_136
    | spl10_68 ),
    inference(avatar_split_clause,[],[f2501,f2493,f3928])).

fof(f3928,plain,
    ( spl10_136
  <=> r2_hidden(sK2,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f2493,plain,
    ( spl10_68
  <=> m1_subset_1(sK2,sK9(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f2501,plain,
    ( ~ r2_hidden(sK2,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(u1_struct_0(sK0))))))
    | spl10_68 ),
    inference(unit_resulting_resolution,[],[f105,f2495,f111])).

fof(f2495,plain,
    ( ~ m1_subset_1(sK2,sK9(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl10_68 ),
    inference(avatar_component_clause,[],[f2493])).

fof(f3926,plain,
    ( spl10_135
    | ~ spl10_63 ),
    inference(avatar_split_clause,[],[f2451,f1874,f3923])).

fof(f3923,plain,
    ( spl10_135
  <=> m1_subset_1(k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_135])])).

fof(f2451,plain,
    ( m1_subset_1(k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK1)
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f1876,f106])).

fof(f3921,plain,
    ( ~ spl10_134
    | spl10_46 ),
    inference(avatar_split_clause,[],[f899,f895,f3918])).

fof(f3918,plain,
    ( spl10_134
  <=> r2_hidden(k13_lattice3(sK0,sK2,sK2),sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f895,plain,
    ( spl10_46
  <=> m1_subset_1(k13_lattice3(sK0,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f899,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,sK2),sK9(k1_zfmisc_1(sK1)))
    | spl10_46 ),
    inference(unit_resulting_resolution,[],[f105,f897,f111])).

fof(f897,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK2,sK2),sK1)
    | spl10_46 ),
    inference(avatar_component_clause,[],[f895])).

fof(f3800,plain,
    ( spl10_133
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f471,f415,f266,f183,f148,f128,f3797])).

fof(f3797,plain,
    ( spl10_133
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_133])])).

fof(f471,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK6(sK0,sK1))
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f130,f150,f268,f417,f92])).

fof(f3793,plain,
    ( spl10_132
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f441,f410,f266,f183,f148,f128,f3790])).

fof(f3790,plain,
    ( spl10_132
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f441,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK5(sK0,sK1))
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f130,f150,f268,f412,f92])).

fof(f3779,plain,
    ( spl10_131
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f294,f266,f183,f148,f128,f3776])).

fof(f3776,plain,
    ( spl10_131
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK9(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_131])])).

fof(f294,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK9(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22 ),
    inference(unit_resulting_resolution,[],[f185,f130,f150,f105,f268,f92])).

fof(f3747,plain,
    ( spl10_130
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_60
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f2357,f1869,f1859,f415,f410,f183,f148,f143,f133,f128,f3744])).

fof(f3744,plain,
    ( spl10_130
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f2357,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_60
    | ~ spl10_62 ),
    inference(backward_demodulation,[],[f460,f2355])).

fof(f2355,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK5(sK0,sK1)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_60
    | ~ spl10_62 ),
    inference(forward_demodulation,[],[f2354,f456])).

fof(f2354,plain,
    ( k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))) = k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK5(sK0,sK1)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_60
    | ~ spl10_62 ),
    inference(forward_demodulation,[],[f2343,f460])).

fof(f2343,plain,
    ( k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_60
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f1861,f1871,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

fof(f460,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK5(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f412,f417,f89])).

fof(f3742,plain,
    ( ~ spl10_12
    | spl10_129
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f705,f163,f158,f153,f148,f138,f128,f123,f118,f3740,f168])).

fof(f168,plain,
    ( spl10_12
  <=> v2_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f3740,plain,
    ( spl10_129
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_129])])).

fof(f118,plain,
    ( spl10_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f123,plain,
    ( spl10_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f138,plain,
    ( spl10_6
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f705,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v2_waybel_7(sK1,sK0) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f704,f165])).

fof(f704,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v2_waybel_7(sK1,sK0) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f699,f155])).

fof(f699,plain,
    ( ! [X0,X1] :
        ( ~ v2_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v2_waybel_7(sK1,sK0) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(resolution,[],[f288,f160])).

fof(f288,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X0,sK0)
        | ~ v2_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X1,X2),X0)
        | r2_hidden(X1,X0)
        | r2_hidden(X2,X0)
        | ~ v2_waybel_7(X0,sK0) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f287,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f287,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,sK0)
        | ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X1,X2),X0)
        | r2_hidden(X1,X0)
        | r2_hidden(X2,X0)
        | ~ v2_waybel_7(X0,sK0) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f286,f120])).

fof(f120,plain,
    ( v3_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f286,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,sK0)
        | ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X1,X2),X0)
        | r2_hidden(X1,X0)
        | r2_hidden(X2,X0)
        | ~ v2_waybel_7(X0,sK0) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f285,f140])).

fof(f140,plain,
    ( v1_lattice3(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f285,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,sK0)
        | ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X1,X2),X0)
        | r2_hidden(X1,X0)
        | r2_hidden(X2,X0)
        | ~ v2_waybel_7(X0,sK0) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f284,f130])).

fof(f284,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,sK0)
        | ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X1,X2),X0)
        | r2_hidden(X1,X0)
        | r2_hidden(X2,X0)
        | ~ v2_waybel_7(X0,sK0) )
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f283,f125])).

fof(f125,plain,
    ( v4_orders_2(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f283,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,sK0)
        | ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(k13_lattice3(sK0,X1,X2),X0)
        | r2_hidden(X1,X0)
        | r2_hidden(X2,X0)
        | ~ v2_waybel_7(X0,sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f97,f150])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v2_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_7)).

fof(f3738,plain,
    ( spl10_128
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f483,f415,f183,f148,f143,f133,f128,f3735])).

fof(f3735,plain,
    ( spl10_128
  <=> k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK6(sK0,sK1))) = k7_waybel_1(sK0,k12_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f483,plain,
    ( k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK6(sK0,sK1))) = k7_waybel_1(sK0,k12_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(forward_demodulation,[],[f466,f480])).

fof(f480,plain,
    ( k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK6(sK0,sK1)) = k12_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f105,f417,f110])).

fof(f466,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f105,f417,f90])).

fof(f3712,plain,
    ( spl10_127
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f481,f415,f410,f183,f148,f143,f133,f128,f3709])).

fof(f3709,plain,
    ( spl10_127
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_127])])).

fof(f481,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(forward_demodulation,[],[f468,f478])).

fof(f478,plain,
    ( k12_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)) = k12_lattice3(sK0,sK6(sK0,sK1),sK5(sK0,sK1))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f412,f417,f110])).

fof(f468,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK6(sK0,sK1),sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f412,f417,f90])).

fof(f3707,plain,
    ( spl10_126
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f470,f415,f183,f148,f133,f3704])).

fof(f3704,plain,
    ( spl10_126
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f470,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f105,f417,f90])).

fof(f3702,plain,
    ( spl10_125
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f469,f415,f183,f148,f133,f3699])).

fof(f3699,plain,
    ( spl10_125
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,sK6(sK0,sK1),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_125])])).

fof(f469,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK6(sK0,sK1),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f417,f417,f90])).

fof(f3697,plain,
    ( spl10_124
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f464,f415,f410,f183,f148,f133,f3694])).

fof(f3694,plain,
    ( spl10_124
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f464,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f412,f417,f90])).

fof(f3691,plain,
    ( spl10_123
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f462,f415,f183,f148,f133,f3688])).

fof(f3688,plain,
    ( spl10_123
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_123])])).

fof(f462,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f105,f417,f89])).

fof(f3686,plain,
    ( spl10_122
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f461,f415,f183,f148,f133,f3683])).

fof(f3683,plain,
    ( spl10_122
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f3681,plain,
    ( spl10_121
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f456,f415,f410,f183,f148,f133,f3678])).

fof(f3678,plain,
    ( spl10_121
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_121])])).

fof(f3676,plain,
    ( spl10_120
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f450,f410,f183,f148,f143,f133,f128,f3673])).

fof(f3673,plain,
    ( spl10_120
  <=> k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK5(sK0,sK1))) = k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_120])])).

fof(f450,plain,
    ( k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK5(sK0,sK1))) = k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(forward_demodulation,[],[f437,f448])).

fof(f448,plain,
    ( k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK5(sK0,sK1)) = k12_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f105,f412,f110])).

fof(f437,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f105,f412,f90])).

fof(f3670,plain,
    ( spl10_119
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f440,f410,f183,f148,f133,f3667])).

fof(f3667,plain,
    ( spl10_119
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).

fof(f440,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f105,f412,f90])).

fof(f3665,plain,
    ( spl10_118
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f439,f410,f183,f148,f133,f3662])).

fof(f3662,plain,
    ( spl10_118
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).

fof(f439,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f412,f412,f90])).

fof(f3660,plain,
    ( spl10_117
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f434,f410,f183,f148,f133,f3657])).

fof(f3657,plain,
    ( spl10_117
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_117])])).

fof(f434,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f105,f412,f89])).

fof(f3655,plain,
    ( spl10_116
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f433,f410,f183,f148,f133,f3652])).

fof(f3652,plain,
    ( spl10_116
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK5(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f3650,plain,
    ( spl10_115
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(avatar_split_clause,[],[f255,f183,f148,f133,f3647])).

fof(f3647,plain,
    ( spl10_115
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_115])])).

fof(f255,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f135,f150,f185,f105,f105,f90])).

fof(f3645,plain,
    ( spl10_114
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(avatar_split_clause,[],[f248,f183,f148,f133,f3642])).

fof(f3642,plain,
    ( spl10_114
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f248,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f135,f150,f185,f105,f105,f89])).

fof(f3602,plain,
    ( ~ spl10_113
    | spl10_105 ),
    inference(avatar_split_clause,[],[f3318,f3270,f3599])).

fof(f3599,plain,
    ( spl10_113
  <=> r2_hidden(k3_yellow_0(sK0),sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_113])])).

fof(f3318,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK9(k1_zfmisc_1(sK1)))
    | spl10_105 ),
    inference(unit_resulting_resolution,[],[f105,f3272,f111])).

fof(f3597,plain,
    ( spl10_112
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35
    | ~ spl10_59
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f2359,f1869,f1854,f415,f183,f148,f143,f133,f128,f3594])).

fof(f3594,plain,
    ( spl10_112
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),sK6(sK0,sK1))) = k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_112])])).

fof(f2359,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),sK6(sK0,sK1))) = k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35
    | ~ spl10_59
    | ~ spl10_62 ),
    inference(backward_demodulation,[],[f458,f2358])).

fof(f2358,plain,
    ( k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK6(sK0,sK1))) = k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35
    | ~ spl10_59
    | ~ spl10_62 ),
    inference(forward_demodulation,[],[f2342,f462])).

fof(f2342,plain,
    ( k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_59
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f1856,f1871,f110])).

fof(f458,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f105,f417,f89])).

fof(f3592,plain,
    ( spl10_111
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_59
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f2144,f1859,f1854,f410,f183,f148,f143,f133,f128,f3589])).

fof(f3589,plain,
    ( spl10_111
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),sK5(sK0,sK1))) = k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_111])])).

fof(f2144,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),sK5(sK0,sK1))) = k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_59
    | ~ spl10_60 ),
    inference(backward_demodulation,[],[f431,f2143])).

fof(f2143,plain,
    ( k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK5(sK0,sK1))) = k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34
    | ~ spl10_59
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f2132,f434])).

fof(f2132,plain,
    ( k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK5(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_59
    | ~ spl10_60 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f1856,f1861,f110])).

fof(f431,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),sK5(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f105,f412,f89])).

fof(f3493,plain,
    ( ~ spl10_110
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_26
    | ~ spl10_57
    | spl10_96 ),
    inference(avatar_split_clause,[],[f3240,f3204,f1636,f314,f163,f158,f148,f3490])).

fof(f3490,plain,
    ( spl10_110
  <=> r1_orders_2(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_110])])).

fof(f1636,plain,
    ( spl10_57
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f3240,plain,
    ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_26
    | ~ spl10_57
    | spl10_96 ),
    inference(unit_resulting_resolution,[],[f316,f160,f165,f1638,f3206,f247])).

fof(f1638,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f1636])).

fof(f3449,plain,
    ( spl10_109
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f881,f494,f163,f158,f153,f148,f143,f128,f3446])).

fof(f3446,plain,
    ( spl10_109
  <=> r2_hidden(k12_lattice3(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_109])])).

fof(f881,plain,
    ( r2_hidden(k12_lattice3(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f496,f155,f160,f165,f496,f281])).

fof(f3393,plain,
    ( ~ spl10_108
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_57
    | spl10_96 ),
    inference(avatar_split_clause,[],[f3243,f3204,f1636,f300,f163,f158,f148,f3390])).

fof(f3390,plain,
    ( spl10_108
  <=> r1_orders_2(sK0,sK9(sK1),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f3243,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1),k3_yellow_0(sK0))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_57
    | spl10_96 ),
    inference(unit_resulting_resolution,[],[f302,f160,f165,f1638,f3206,f247])).

fof(f3283,plain,
    ( spl10_107
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48
    | ~ spl10_57
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f2353,f1869,f1636,f912,f415,f309,f183,f148,f143,f133,f128,f3280])).

fof(f3280,plain,
    ( spl10_107
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),k4_yellow_0(sK0))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_107])])).

fof(f2353,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),k4_yellow_0(sK0))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48
    | ~ spl10_57
    | ~ spl10_62 ),
    inference(backward_demodulation,[],[f1481,f2345])).

fof(f2345,plain,
    ( k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_57
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f1638,f1871,f110])).

fof(f1481,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),k4_yellow_0(sK0))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k3_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f459,f1467])).

fof(f459,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK6(sK0,sK1),k4_yellow_0(sK0))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f311,f417,f89])).

fof(f3278,plain,
    ( spl10_106
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48
    | ~ spl10_57
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f2142,f1859,f1636,f912,f410,f309,f183,f148,f143,f133,f128,f3275])).

fof(f3275,plain,
    ( spl10_106
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),k4_yellow_0(sK0))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f2142,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),k4_yellow_0(sK0))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48
    | ~ spl10_57
    | ~ spl10_60 ),
    inference(backward_demodulation,[],[f1477,f2134])).

fof(f2134,plain,
    ( k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_57
    | ~ spl10_60 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f1638,f1861,f110])).

fof(f1477,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),k4_yellow_0(sK0))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k3_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f432,f1467])).

fof(f432,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),k4_yellow_0(sK0))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f311,f412,f89])).

fof(f3273,plain,
    ( ~ spl10_105
    | spl10_1
    | spl10_96 ),
    inference(avatar_split_clause,[],[f3236,f3204,f113,f3270])).

fof(f3236,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl10_1
    | spl10_96 ),
    inference(unit_resulting_resolution,[],[f115,f3206,f107])).

fof(f3268,plain,
    ( spl10_104
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48
    | ~ spl10_57
    | ~ spl10_59 ),
    inference(avatar_split_clause,[],[f1968,f1854,f1636,f912,f309,f183,f148,f143,f133,f128,f3265])).

fof(f3265,plain,
    ( spl10_104
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),k4_yellow_0(sK0))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f1968,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),k4_yellow_0(sK0))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48
    | ~ spl10_57
    | ~ spl10_59 ),
    inference(backward_demodulation,[],[f1470,f1961])).

fof(f1961,plain,
    ( k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k3_yellow_0(sK0)) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_57
    | ~ spl10_59 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f1638,f1856,f110])).

fof(f1470,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),k4_yellow_0(sK0))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k3_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f327,f1467])).

fof(f327,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK9(u1_struct_0(sK0)),k4_yellow_0(sK0))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f105,f311,f89])).

fof(f3263,plain,
    ( spl10_103
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1520,f912,f415,f309,f183,f148,f143,f133,f128,f3260])).

fof(f3260,plain,
    ( spl10_103
  <=> k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_103])])).

fof(f1520,plain,
    ( k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f1483,f1482])).

fof(f1482,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))) = k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f463,f1467])).

fof(f463,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f311,f417,f90])).

fof(f1483,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f482,f1467])).

fof(f482,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35 ),
    inference(forward_demodulation,[],[f467,f477])).

fof(f477,plain,
    ( k12_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1)) = k12_lattice3(sK0,sK6(sK0,sK1),k4_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_25
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f311,f417,f110])).

fof(f467,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK6(sK0,sK1),k4_yellow_0(sK0))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK6(sK0,sK1)),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f311,f417,f90])).

fof(f3258,plain,
    ( spl10_102
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1519,f912,f410,f309,f183,f148,f143,f133,f128,f3255])).

fof(f3255,plain,
    ( spl10_102
  <=> k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f1519,plain,
    ( k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f1479,f1478])).

fof(f1478,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))) = k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f435,f1467])).

fof(f435,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f311,f412,f90])).

fof(f1479,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f449,f1467])).

fof(f449,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34 ),
    inference(forward_demodulation,[],[f438,f446])).

fof(f446,plain,
    ( k12_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1)) = k12_lattice3(sK0,sK5(sK0,sK1),k4_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_25
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f311,f412,f110])).

fof(f438,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK5(sK0,sK1),k4_yellow_0(sK0))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f311,f412,f90])).

fof(f3253,plain,
    ( spl10_101
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1518,f912,f309,f183,f148,f143,f133,f128,f3250])).

fof(f3250,plain,
    ( spl10_101
  <=> k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).

fof(f1518,plain,
    ( k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f1475,f1474])).

fof(f1474,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f336,f1467])).

fof(f336,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f105,f311,f90])).

fof(f1475,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f346,f1467])).

fof(f346,plain,
    ( k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,k4_yellow_0(sK0))) = k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0))))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(forward_demodulation,[],[f333,f344])).

fof(f344,plain,
    ( k12_lattice3(sK0,sK9(u1_struct_0(sK0)),k4_yellow_0(sK0)) = k12_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f145,f130,f150,f105,f311,f110])).

fof(f333,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,sK9(u1_struct_0(sK0)),k4_yellow_0(sK0))) = k13_lattice3(sK0,k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f105,f311,f90])).

fof(f3227,plain,
    ( spl10_100
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1482,f912,f415,f309,f183,f148,f133,f3224])).

fof(f3224,plain,
    ( spl10_100
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))) = k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f3222,plain,
    ( spl10_99
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1480,f912,f415,f309,f183,f148,f133,f3219])).

fof(f3219,plain,
    ( spl10_99
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f1480,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f455,f1467])).

fof(f455,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f311,f417,f89])).

fof(f3217,plain,
    ( spl10_98
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1478,f912,f410,f309,f183,f148,f133,f3214])).

fof(f3214,plain,
    ( spl10_98
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))) = k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f3212,plain,
    ( spl10_97
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1476,f912,f410,f309,f183,f148,f133,f3209])).

fof(f3209,plain,
    ( spl10_97
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f1476,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f429,f1467])).

fof(f429,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f311,f412,f89])).

fof(f3207,plain,
    ( ~ spl10_96
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_22
    | spl10_31
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f3191,f415,f391,f266,f183,f163,f158,f148,f128,f3204])).

fof(f3191,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_22
    | spl10_31
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f160,f393,f417,f165,f596])).

fof(f596,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1)
        | ~ v13_waybel_0(X1,sK0) )
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f595,f185])).

fof(f595,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1)
        | ~ v13_waybel_0(X1,sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f594,f150])).

fof(f594,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1)
        | ~ v13_waybel_0(X1,sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f593,f268])).

fof(f593,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1)
        | ~ v13_waybel_0(X1,sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f592,f130])).

fof(f592,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1)
        | ~ v13_waybel_0(X1,sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_8 ),
    inference(duplicate_literal_removal,[],[f590])).

fof(f590,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1)
        | ~ v13_waybel_0(X1,sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f247,f92])).

fof(f3202,plain,
    ( spl10_95
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1474,f912,f309,f183,f148,f133,f3199])).

fof(f3199,plain,
    ( spl10_95
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0)))) = k13_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).

fof(f3197,plain,
    ( spl10_94
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1472,f912,f309,f183,f148,f133,f3194])).

fof(f3194,plain,
    ( spl10_94
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f1472,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f330,f1467])).

fof(f330,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0)))) = k12_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f105,f311,f89])).

fof(f3185,plain,
    ( spl10_93
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f480,f415,f148,f143,f128,f3182])).

fof(f3182,plain,
    ( spl10_93
  <=> k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK6(sK0,sK1)) = k12_lattice3(sK0,sK6(sK0,sK1),sK9(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f3180,plain,
    ( spl10_92
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f478,f415,f410,f148,f143,f128,f3177])).

fof(f3177,plain,
    ( spl10_92
  <=> k12_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)) = k12_lattice3(sK0,sK6(sK0,sK1),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f3174,plain,
    ( spl10_91
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f448,f410,f148,f143,f128,f3171])).

fof(f3171,plain,
    ( spl10_91
  <=> k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK5(sK0,sK1)) = k12_lattice3(sK0,sK5(sK0,sK1),sK9(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f2887,plain,
    ( spl10_90
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1473,f912,f309,f183,f148,f133,f2884])).

fof(f2884,plain,
    ( spl10_90
  <=> k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))) = k13_lattice3(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f1473,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))) = k13_lattice3(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f334,f1467])).

fof(f334,plain,
    ( k7_waybel_1(sK0,k12_lattice3(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))) = k13_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f311,f311,f90])).

fof(f2882,plain,
    ( spl10_89
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1471,f912,f309,f183,f148,f133,f2879])).

fof(f2879,plain,
    ( spl10_89
  <=> k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))) = k12_lattice3(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f1471,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))) = k12_lattice3(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f328,f1467])).

fof(f328,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))) = k12_lattice3(sK0,k7_waybel_1(sK0,k4_yellow_0(sK0)),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f150,f135,f311,f311,f89])).

fof(f2877,plain,
    ( spl10_88
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1467,f912,f309,f183,f148,f133,f2874])).

fof(f2874,plain,
    ( spl10_88
  <=> k3_yellow_0(sK0) = k7_waybel_1(sK0,k4_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f2872,plain,
    ( spl10_87
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_25
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f477,f415,f309,f148,f143,f128,f2869])).

fof(f2869,plain,
    ( spl10_87
  <=> k12_lattice3(sK0,k4_yellow_0(sK0),sK6(sK0,sK1)) = k12_lattice3(sK0,sK6(sK0,sK1),k4_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f2867,plain,
    ( spl10_86
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_25
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f446,f410,f309,f148,f143,f128,f2864])).

fof(f2864,plain,
    ( spl10_86
  <=> k12_lattice3(sK0,k4_yellow_0(sK0),sK5(sK0,sK1)) = k12_lattice3(sK0,sK5(sK0,sK1),k4_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f2862,plain,
    ( spl10_85
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f344,f309,f148,f143,f128,f2859])).

fof(f2859,plain,
    ( spl10_85
  <=> k12_lattice3(sK0,sK9(u1_struct_0(sK0)),k4_yellow_0(sK0)) = k12_lattice3(sK0,k4_yellow_0(sK0),sK9(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).

fof(f2823,plain,
    ( spl10_84
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1465,f912,f309,f183,f148,f133,f2820])).

fof(f2820,plain,
    ( spl10_84
  <=> k4_yellow_0(sK0) = k7_waybel_1(sK0,k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f2818,plain,
    ( spl10_83
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f879,f494,f300,f163,f158,f153,f148,f143,f128,f2815])).

fof(f2815,plain,
    ( spl10_83
  <=> r2_hidden(k12_lattice3(sK0,sK9(sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f879,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f302,f155,f160,f165,f496,f281])).

fof(f2813,plain,
    ( ~ spl10_82
    | spl10_43 ),
    inference(avatar_split_clause,[],[f844,f733,f2810])).

fof(f2810,plain,
    ( spl10_82
  <=> r2_hidden(u1_struct_0(sK0),sK9(k1_zfmisc_1(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f733,plain,
    ( spl10_43
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f844,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK9(k1_zfmisc_1(k1_zfmisc_1(sK1))))
    | spl10_43 ),
    inference(unit_resulting_resolution,[],[f105,f735,f111])).

fof(f735,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1))
    | spl10_43 ),
    inference(avatar_component_clause,[],[f733])).

fof(f2806,plain,
    ( ~ spl10_81
    | spl10_42 ),
    inference(avatar_split_clause,[],[f841,f727,f2803])).

fof(f2803,plain,
    ( spl10_81
  <=> r2_hidden(sK5(sK0,sK1),sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).

fof(f727,plain,
    ( spl10_42
  <=> m1_subset_1(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f841,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK9(k1_zfmisc_1(sK1)))
    | spl10_42 ),
    inference(unit_resulting_resolution,[],[f105,f729,f111])).

fof(f729,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),sK1)
    | spl10_42 ),
    inference(avatar_component_clause,[],[f727])).

fof(f2800,plain,
    ( ~ spl10_80
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | ~ spl10_35
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f875,f494,f415,f391,f163,f158,f148,f2797])).

fof(f2797,plain,
    ( spl10_80
  <=> r1_orders_2(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f875,plain,
    ( ~ r1_orders_2(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK6(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | ~ spl10_35
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f160,f393,f417,f165,f496,f247])).

fof(f2795,plain,
    ( ~ spl10_79
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_32
    | ~ spl10_34
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f874,f494,f410,f396,f163,f158,f148,f2792])).

fof(f2792,plain,
    ( spl10_79
  <=> r1_orders_2(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f874,plain,
    ( ~ r1_orders_2(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK5(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_32
    | ~ spl10_34
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f160,f398,f412,f165,f496,f247])).

fof(f2790,plain,
    ( spl10_78
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f454,f415,f183,f148,f133,f2787])).

fof(f2787,plain,
    ( spl10_78
  <=> k4_yellow_0(sK0) = k13_lattice3(sK0,sK6(sK0,sK1),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f454,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,sK6(sK0,sK1),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f417,f88])).

fof(f2785,plain,
    ( ~ spl10_77
    | spl10_41 ),
    inference(avatar_split_clause,[],[f838,f722,f2782])).

fof(f2782,plain,
    ( spl10_77
  <=> r2_hidden(sK6(sK0,sK1),sK9(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f722,plain,
    ( spl10_41
  <=> m1_subset_1(sK6(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f838,plain,
    ( ~ r2_hidden(sK6(sK0,sK1),sK9(k1_zfmisc_1(sK1)))
    | spl10_41 ),
    inference(unit_resulting_resolution,[],[f105,f724,f111])).

fof(f724,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | spl10_41 ),
    inference(avatar_component_clause,[],[f722])).

fof(f2780,plain,
    ( spl10_76
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f453,f415,f183,f148,f133,f2777])).

fof(f2777,plain,
    ( spl10_76
  <=> k3_yellow_0(sK0) = k12_lattice3(sK0,sK6(sK0,sK1),k7_waybel_1(sK0,sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f453,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,sK6(sK0,sK1),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f417,f87])).

fof(f2775,plain,
    ( spl10_75
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f428,f410,f183,f148,f133,f2772])).

fof(f2772,plain,
    ( spl10_75
  <=> k4_yellow_0(sK0) = k13_lattice3(sK0,sK5(sK0,sK1),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f428,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,sK5(sK0,sK1),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f412,f88])).

fof(f2770,plain,
    ( spl10_74
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f427,f410,f183,f148,f133,f2767])).

fof(f2767,plain,
    ( spl10_74
  <=> k3_yellow_0(sK0) = k12_lattice3(sK0,sK5(sK0,sK1),k7_waybel_1(sK0,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f427,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,sK5(sK0,sK1),k7_waybel_1(sK0,sK5(sK0,sK1)))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f412,f87])).

fof(f2765,plain,
    ( spl10_73
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(avatar_split_clause,[],[f232,f183,f148,f133,f2762])).

fof(f2762,plain,
    ( spl10_73
  <=> k4_yellow_0(sK0) = k13_lattice3(sK0,sK9(u1_struct_0(sK0)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f232,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,sK9(u1_struct_0(sK0)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f105,f88])).

fof(f2760,plain,
    ( spl10_72
    | ~ spl10_8
    | spl10_15
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f812,f717,f183,f148,f2757])).

fof(f812,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK9(sK1)),u1_struct_0(sK0))
    | ~ spl10_8
    | spl10_15
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f185,f150,f719,f108])).

fof(f2755,plain,
    ( spl10_71
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(avatar_split_clause,[],[f230,f183,f148,f133,f2752])).

fof(f2752,plain,
    ( spl10_71
  <=> k3_yellow_0(sK0) = k12_lattice3(sK0,sK9(u1_struct_0(sK0)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f230,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,sK9(u1_struct_0(sK0)),k7_waybel_1(sK0,sK9(u1_struct_0(sK0))))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f105,f87])).

fof(f2509,plain,
    ( spl10_70
    | ~ spl10_11
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f873,f494,f163,f2506])).

fof(f873,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_11
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f165,f496,f111])).

fof(f2500,plain,
    ( ~ spl10_68
    | spl10_69
    | spl10_36 ),
    inference(avatar_split_clause,[],[f484,f421,f2497,f2493])).

fof(f2497,plain,
    ( spl10_69
  <=> v1_xboole_0(sK9(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f421,plain,
    ( spl10_36
  <=> r2_hidden(sK2,sK9(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f484,plain,
    ( v1_xboole_0(sK9(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,sK9(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl10_36 ),
    inference(resolution,[],[f423,f107])).

fof(f423,plain,
    ( ~ r2_hidden(sK2,sK9(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl10_36 ),
    inference(avatar_component_clause,[],[f421])).

fof(f2490,plain,
    ( spl10_67
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f871,f494,f2487])).

fof(f2487,plain,
    ( spl10_67
  <=> m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f871,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f496,f106])).

fof(f2482,plain,
    ( spl10_66
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1469,f912,f309,f183,f148,f133,f2479])).

fof(f2479,plain,
    ( spl10_66
  <=> k4_yellow_0(sK0) = k13_lattice3(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f1469,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f324,f1467])).

fof(f2476,plain,
    ( spl10_65
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1468,f912,f309,f183,f148,f133,f2473])).

fof(f2473,plain,
    ( spl10_65
  <=> k3_yellow_0(sK0) = k12_lattice3(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f1468,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f323,f1467])).

fof(f2227,plain,
    ( spl10_64
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1504,f912,f309,f266,f183,f148,f133,f128,f2224])).

fof(f2224,plain,
    ( spl10_64
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f1504,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f1437,f1467])).

fof(f1437,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k7_waybel_1(sK0,k4_yellow_0(sK0)))
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_48 ),
    inference(unit_resulting_resolution,[],[f185,f130,f150,f268,f914,f92])).

fof(f1877,plain,
    ( spl10_63
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f677,f300,f163,f158,f153,f148,f143,f128,f1874])).

fof(f677,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK1),sK9(sK1)),sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f302,f302,f155,f160,f165,f281])).

fof(f1872,plain,
    ( spl10_62
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f472,f415,f183,f148,f1869])).

fof(f472,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_8
    | spl10_15
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f185,f150,f417,f108])).

fof(f1867,plain,
    ( spl10_61
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f807,f717,f266,f183,f148,f128,f1864])).

fof(f1864,plain,
    ( spl10_61
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK9(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f807,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK9(sK1))
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f185,f130,f150,f268,f719,f92])).

fof(f1862,plain,
    ( spl10_60
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f442,f410,f183,f148,f1859])).

fof(f442,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_8
    | spl10_15
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f185,f150,f412,f108])).

fof(f1857,plain,
    ( spl10_59
    | ~ spl10_8
    | spl10_15 ),
    inference(avatar_split_clause,[],[f223,f183,f148,f1854])).

fof(f223,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK9(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl10_8
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f185,f150,f105,f108])).

fof(f1850,plain,
    ( spl10_58
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f337,f309,f266,f183,f148,f128,f1847])).

fof(f1847,plain,
    ( spl10_58
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f337,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0))
    | ~ spl10_4
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f130,f150,f268,f311,f92])).

fof(f1639,plain,
    ( spl10_57
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1488,f912,f309,f183,f148,f133,f1636])).

fof(f1488,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f914,f1467])).

fof(f1374,plain,
    ( ~ spl10_56
    | spl10_43 ),
    inference(avatar_split_clause,[],[f845,f733,f1371])).

fof(f1371,plain,
    ( spl10_56
  <=> r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f845,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK1))
    | spl10_43 ),
    inference(unit_resulting_resolution,[],[f735,f106])).

fof(f1369,plain,
    ( spl10_55
    | ~ spl10_18
    | spl10_31
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f886,f415,f391,f211,f1366])).

fof(f1366,plain,
    ( spl10_55
  <=> m1_subset_1(k7_waybel_1(sK0,sK6(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f211,plain,
    ( spl10_18
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(k7_waybel_1(sK0,X2),sK1)
        | r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f886,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK6(sK0,sK1)),sK1)
    | ~ spl10_18
    | spl10_31
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f393,f417,f388])).

fof(f388,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_waybel_1(sK0,X0),sK1)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_18 ),
    inference(resolution,[],[f212,f106])).

fof(f212,plain,
    ( ! [X2] :
        ( r2_hidden(k7_waybel_1(sK0,X2),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,sK1) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f1364,plain,
    ( spl10_54
    | ~ spl10_18
    | spl10_32
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f885,f410,f396,f211,f1361])).

fof(f1361,plain,
    ( spl10_54
  <=> m1_subset_1(k7_waybel_1(sK0,sK5(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f885,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK5(sK0,sK1)),sK1)
    | ~ spl10_18
    | spl10_32
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f398,f412,f388])).

fof(f1359,plain,
    ( ~ spl10_53
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | spl10_31
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f588,f415,f391,f300,f163,f158,f148,f1356])).

fof(f1356,plain,
    ( spl10_53
  <=> r1_orders_2(sK0,sK9(sK1),sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f588,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1),sK6(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | spl10_31
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f302,f160,f393,f417,f165,f247])).

fof(f1354,plain,
    ( ~ spl10_52
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | spl10_32
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f586,f410,f396,f300,f163,f158,f148,f1351])).

fof(f1351,plain,
    ( spl10_52
  <=> r1_orders_2(sK0,sK9(sK1),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f586,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1),sK5(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_24
    | spl10_32
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f302,f160,f398,f412,f165,f247])).

fof(f1347,plain,
    ( spl10_51
    | ~ spl10_18
    | spl10_31
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f451,f415,f391,f211,f1344])).

fof(f451,plain,
    ( r2_hidden(k7_waybel_1(sK0,sK6(sK0,sK1)),sK1)
    | ~ spl10_18
    | spl10_31
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f393,f417,f212])).

fof(f1320,plain,
    ( ~ spl10_14
    | spl10_13
    | ~ spl10_18
    | spl10_27 ),
    inference(avatar_split_clause,[],[f887,f319,f211,f172,f177])).

fof(f177,plain,
    ( spl10_14
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f172,plain,
    ( spl10_13
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f319,plain,
    ( spl10_27
  <=> m1_subset_1(k7_waybel_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f887,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl10_13
    | ~ spl10_18
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f174,f321,f388])).

fof(f321,plain,
    ( ~ m1_subset_1(k7_waybel_1(sK0,sK2),sK1)
    | spl10_27 ),
    inference(avatar_component_clause,[],[f319])).

fof(f174,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1168,plain,
    ( ~ spl10_12
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | spl10_32
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f882,f494,f415,f410,f396,f391,f163,f158,f153,f148,f138,f128,f123,f118,f168])).

fof(f882,plain,
    ( ~ v2_waybel_7(sK1,sK0)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_31
    | spl10_32
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f160,f155,f393,f398,f165,f417,f412,f496,f288])).

fof(f1129,plain,
    ( ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | spl10_15
    | spl10_16
    | ~ spl10_26
    | ~ spl10_45 ),
    inference(avatar_contradiction_clause,[],[f1128])).

fof(f1128,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | spl10_15
    | spl10_16
    | ~ spl10_26
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f1127,f316])).

fof(f1127,plain,
    ( ~ r2_hidden(k4_yellow_0(sK0),sK1)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | spl10_15
    | spl10_16
    | ~ spl10_45 ),
    inference(forward_demodulation,[],[f1038,f233])).

fof(f233,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,sK2,k7_waybel_1(sK0,sK2))
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_14
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f185,f135,f150,f179,f88])).

fof(f179,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1038,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,k7_waybel_1(sK0,sK2)),sK1)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | spl10_16
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f169,f174,f179,f155,f160,f190,f165,f850,f288])).

fof(f850,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f848])).

fof(f848,plain,
    ( spl10_45
  <=> m1_subset_1(k7_waybel_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f190,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK2),sK1)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_16
  <=> r2_hidden(k7_waybel_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f169,plain,
    ( v2_waybel_7(sK1,sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f1085,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | spl10_15
    | spl10_16
    | ~ spl10_26
    | ~ spl10_45 ),
    inference(avatar_contradiction_clause,[],[f1084])).

fof(f1084,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | spl10_15
    | spl10_16
    | ~ spl10_26
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f1083,f316])).

fof(f1083,plain,
    ( ~ r2_hidden(k4_yellow_0(sK0),sK1)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | spl10_15
    | spl10_16
    | ~ spl10_45 ),
    inference(forward_demodulation,[],[f1069,f233])).

fof(f1069,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,k7_waybel_1(sK0,sK2)),sK1)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | spl10_16
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f130,f140,f115,f125,f150,f120,f169,f174,f179,f160,f155,f190,f165,f850,f97])).

fof(f925,plain,
    ( spl10_50
    | ~ spl10_18
    | spl10_32
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f425,f410,f396,f211,f922])).

fof(f425,plain,
    ( r2_hidden(k7_waybel_1(sK0,sK5(sK0,sK1)),sK1)
    | ~ spl10_18
    | spl10_32
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f398,f412,f212])).

fof(f920,plain,
    ( ~ spl10_49
    | spl10_27 ),
    inference(avatar_split_clause,[],[f347,f319,f917])).

fof(f347,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK2),sK9(k1_zfmisc_1(sK1)))
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f105,f321,f111])).

fof(f915,plain,
    ( spl10_48
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f338,f309,f183,f148,f912])).

fof(f338,plain,
    ( m1_subset_1(k7_waybel_1(sK0,k4_yellow_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_8
    | spl10_15
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f185,f150,f311,f108])).

fof(f908,plain,
    ( spl10_47
    | ~ spl10_25
    | spl10_39 ),
    inference(avatar_split_clause,[],[f709,f551,f309,f905])).

fof(f905,plain,
    ( spl10_47
  <=> r2_hidden(k4_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f551,plain,
    ( spl10_39
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f709,plain,
    ( r2_hidden(k4_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl10_25
    | spl10_39 ),
    inference(unit_resulting_resolution,[],[f311,f552,f107])).

fof(f552,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl10_39 ),
    inference(avatar_component_clause,[],[f551])).

fof(f898,plain,
    ( ~ spl10_46
    | spl10_1
    | spl10_28 ),
    inference(avatar_split_clause,[],[f362,f351,f113,f895])).

fof(f351,plain,
    ( spl10_28
  <=> r2_hidden(k13_lattice3(sK0,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f362,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK2,sK2),sK1)
    | spl10_1
    | spl10_28 ),
    inference(unit_resulting_resolution,[],[f115,f353,f107])).

fof(f353,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,sK2),sK1)
    | spl10_28 ),
    inference(avatar_component_clause,[],[f351])).

fof(f889,plain,
    ( ~ spl10_14
    | spl10_30
    | spl10_39 ),
    inference(avatar_split_clause,[],[f852,f551,f382,f177])).

fof(f382,plain,
    ( spl10_30
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f852,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl10_30
    | spl10_39 ),
    inference(subsumption_resolution,[],[f389,f552])).

fof(f389,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl10_30 ),
    inference(resolution,[],[f384,f107])).

fof(f384,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl10_30 ),
    inference(avatar_component_clause,[],[f382])).

fof(f851,plain,
    ( spl10_45
    | ~ spl10_8
    | ~ spl10_14
    | spl10_15 ),
    inference(avatar_split_clause,[],[f224,f183,f177,f148,f848])).

fof(f224,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl10_8
    | ~ spl10_14
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f185,f150,f179,f108])).

fof(f741,plain,
    ( ~ spl10_44
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_13
    | ~ spl10_14
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f584,f300,f177,f172,f163,f158,f148,f738])).

fof(f738,plain,
    ( spl10_44
  <=> r1_orders_2(sK0,sK9(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f584,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1),sK2)
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_11
    | spl10_13
    | ~ spl10_14
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f302,f160,f174,f179,f165,f247])).

fof(f736,plain,
    ( ~ spl10_43
    | spl10_23
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f555,f382,f290,f733])).

fof(f290,plain,
    ( spl10_23
  <=> m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f555,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK1))
    | spl10_23
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f292,f383,f111])).

fof(f383,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f382])).

fof(f292,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | spl10_23 ),
    inference(avatar_component_clause,[],[f290])).

fof(f730,plain,
    ( ~ spl10_42
    | spl10_1
    | spl10_32 ),
    inference(avatar_split_clause,[],[f407,f396,f113,f727])).

fof(f407,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),sK1)
    | spl10_1
    | spl10_32 ),
    inference(unit_resulting_resolution,[],[f115,f398,f107])).

fof(f725,plain,
    ( ~ spl10_41
    | spl10_1
    | spl10_31 ),
    inference(avatar_split_clause,[],[f405,f391,f113,f722])).

fof(f405,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | spl10_1
    | spl10_31 ),
    inference(unit_resulting_resolution,[],[f115,f393,f107])).

fof(f720,plain,
    ( spl10_40
    | ~ spl10_11
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f304,f300,f163,f717])).

fof(f304,plain,
    ( m1_subset_1(sK9(sK1),u1_struct_0(sK0))
    | ~ spl10_11
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f165,f302,f111])).

fof(f598,plain,
    ( ~ spl10_39
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f557,f382,f551])).

fof(f557,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f383,f109])).

fof(f554,plain,
    ( spl10_39
    | ~ spl10_14
    | spl10_30 ),
    inference(avatar_split_clause,[],[f545,f382,f177,f551])).

fof(f545,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_14
    | spl10_30 ),
    inference(unit_resulting_resolution,[],[f384,f179,f107])).

fof(f497,plain,
    ( spl10_38
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f369,f168,f163,f158,f153,f148,f138,f128,f123,f118,f113,f494])).

fof(f369,plain,
    ( r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f120,f125,f130,f150,f140,f115,f160,f155,f165,f170,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k13_lattice3(X0,sK5(X0,X1),sK6(X0,X1)),X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f170,plain,
    ( ~ v2_waybel_7(sK1,sK0)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f489,plain,
    ( ~ spl10_37
    | spl10_23 ),
    inference(avatar_split_clause,[],[f296,f290,f486])).

fof(f296,plain,
    ( ~ r2_hidden(sK2,sK9(k1_zfmisc_1(sK1)))
    | spl10_23 ),
    inference(unit_resulting_resolution,[],[f105,f292,f111])).

fof(f424,plain,
    ( ~ spl10_36
    | spl10_14 ),
    inference(avatar_split_clause,[],[f378,f177,f421])).

fof(f378,plain,
    ( ~ r2_hidden(sK2,sK9(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f105,f178,f111])).

fof(f178,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl10_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f418,plain,
    ( spl10_35
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f371,f168,f163,f158,f153,f148,f138,f128,f123,f118,f113,f415])).

fof(f371,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f125,f120,f130,f150,f140,f115,f160,f155,f165,f170,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f413,plain,
    ( spl10_34
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f370,f168,f163,f158,f153,f148,f138,f128,f123,f118,f113,f410])).

fof(f370,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f125,f120,f130,f150,f140,f115,f160,f155,f165,f170,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f404,plain,
    ( spl10_33
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f359,f314,f401])).

fof(f401,plain,
    ( spl10_33
  <=> m1_subset_1(k4_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f359,plain,
    ( m1_subset_1(k4_yellow_0(sK0),sK1)
    | ~ spl10_26 ),
    inference(unit_resulting_resolution,[],[f316,f106])).

fof(f399,plain,
    ( ~ spl10_32
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f373,f168,f163,f158,f153,f148,f138,f128,f123,f118,f113,f396])).

fof(f373,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f120,f130,f125,f150,f140,f115,f160,f155,f165,f170,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK5(X0,X1),X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f394,plain,
    ( ~ spl10_31
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f372,f168,f163,f158,f153,f148,f138,f128,f123,f118,f113,f391])).

fof(f372,plain,
    ( ~ r2_hidden(sK6(sK0,sK1),sK1)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f120,f130,f125,f150,f140,f115,f160,f155,f165,f170,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK6(X0,X1),X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f385,plain,
    ( ~ spl10_30
    | spl10_14 ),
    inference(avatar_split_clause,[],[f379,f177,f382])).

fof(f379,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f178,f106])).

fof(f368,plain,
    ( spl10_29
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f236,f177,f148,f143,f128,f365])).

fof(f365,plain,
    ( spl10_29
  <=> k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK2) = k12_lattice3(sK0,sK2,sK9(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f236,plain,
    ( k12_lattice3(sK0,sK9(u1_struct_0(sK0)),sK2) = k12_lattice3(sK0,sK2,sK9(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14 ),
    inference(unit_resulting_resolution,[],[f150,f130,f145,f105,f179,f110])).

fof(f354,plain,
    ( ~ spl10_28
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f282,f177,f172,f168,f163,f158,f153,f148,f138,f128,f123,f118,f113,f351])).

fof(f282,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,sK2),sK1)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14 ),
    inference(unit_resulting_resolution,[],[f150,f140,f130,f125,f115,f120,f169,f174,f174,f179,f179,f160,f155,f165,f97])).

fof(f322,plain,
    ( ~ spl10_27
    | spl10_1
    | spl10_16 ),
    inference(avatar_split_clause,[],[f221,f188,f113,f319])).

fof(f221,plain,
    ( ~ m1_subset_1(k7_waybel_1(sK0,sK2),sK1)
    | spl10_1
    | spl10_16 ),
    inference(unit_resulting_resolution,[],[f115,f190,f107])).

fof(f317,plain,
    ( spl10_26
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f270,f242,f183,f163,f158,f153,f148,f128,f123,f118,f113,f314])).

fof(f242,plain,
    ( spl10_21
  <=> v2_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f270,plain,
    ( r2_hidden(k4_yellow_0(sK0),sK1)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_15
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f125,f120,f185,f130,f115,f150,f160,f155,f165,f244,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v2_yellow_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k4_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_4)).

fof(f244,plain,
    ( v2_yellow_0(sK0)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f242])).

fof(f312,plain,
    ( spl10_25
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f192,f148,f309])).

fof(f192,plain,
    ( m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f150,f69])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_0)).

fof(f303,plain,
    ( spl10_24
    | spl10_1 ),
    inference(avatar_split_clause,[],[f206,f113,f300])).

fof(f206,plain,
    ( r2_hidden(sK9(sK1),sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f105,f115,f107])).

fof(f293,plain,
    ( ~ spl10_23
    | spl10_1
    | spl10_13 ),
    inference(avatar_split_clause,[],[f214,f172,f113,f290])).

fof(f214,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | spl10_1
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f115,f174,f107])).

fof(f269,plain,
    ( spl10_22
    | ~ spl10_8
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f209,f200,f148,f266])).

fof(f200,plain,
    ( spl10_17
  <=> v3_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f209,plain,
    ( v1_yellow_0(sK0)
    | ~ spl10_8
    | ~ spl10_17 ),
    inference(unit_resulting_resolution,[],[f150,f202,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_0)).

fof(f202,plain,
    ( v3_yellow_0(sK0)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f245,plain,
    ( spl10_21
    | ~ spl10_8
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f208,f200,f148,f242])).

fof(f208,plain,
    ( v2_yellow_0(sK0)
    | ~ spl10_8
    | ~ spl10_17 ),
    inference(unit_resulting_resolution,[],[f150,f202,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f229,plain,
    ( spl10_20
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(avatar_split_clause,[],[f205,f183,f148,f133,f226])).

fof(f226,plain,
    ( spl10_20
  <=> v10_waybel_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f205,plain,
    ( v10_waybel_1(sK0)
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f150,f135,f185,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v10_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(f220,plain,
    ( spl10_19
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(avatar_split_clause,[],[f204,f183,f148,f133,f217])).

fof(f217,plain,
    ( spl10_19
  <=> v2_waybel_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f204,plain,
    ( v2_waybel_1(sK0)
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f150,f135,f185,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v2_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f213,plain,
    ( spl10_12
    | spl10_18 ),
    inference(avatar_split_clause,[],[f57,f211,f168])).

fof(f57,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,sK1)
      | r2_hidden(k7_waybel_1(sK0,X2),sK1)
      | v2_waybel_7(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_7(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_7(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v11_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v2_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                    | r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_7)).

fof(f203,plain,
    ( spl10_17
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(avatar_split_clause,[],[f198,f183,f148,f133,f200])).

fof(f198,plain,
    ( v3_yellow_0(sK0)
    | ~ spl10_5
    | ~ spl10_8
    | spl10_15 ),
    inference(unit_resulting_resolution,[],[f150,f135,f185,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v3_yellow_0(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f191,plain,
    ( ~ spl10_12
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f56,f188,f168])).

fof(f56,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK2),sK1)
    | ~ v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f186,plain,
    ( ~ spl10_15
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f181,f148,f143,f183])).

fof(f181,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f150,f145,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f180,plain,
    ( ~ spl10_12
    | spl10_14 ),
    inference(avatar_split_clause,[],[f54,f177,f168])).

fof(f54,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f175,plain,
    ( ~ spl10_12
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f55,f172,f168])).

fof(f55,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f166,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f61,f163])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f161,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f60,f158])).

fof(f60,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f156,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f59,f153])).

fof(f59,plain,(
    v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f151,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f68,f148])).

fof(f68,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f146,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f67,f143])).

fof(f67,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f141,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f66,f138])).

fof(f66,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f136,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f65,f133])).

fof(f65,plain,(
    v11_waybel_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f64,f128])).

fof(f64,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f63,f123])).

fof(f63,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f121,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f62,f118])).

fof(f62,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f58,f113])).

fof(f58,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
