%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t35_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:14 EDT 2019

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  770 (2406 expanded)
%              Number of leaves         :  129 (1051 expanded)
%              Depth                    :   25
%              Number of atoms          : 5242 (11220 expanded)
%              Number of equality atoms :  109 ( 277 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4641,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f114,f121,f128,f135,f142,f149,f156,f163,f170,f177,f184,f191,f204,f211,f224,f243,f251,f258,f269,f343,f344,f389,f430,f449,f458,f483,f491,f498,f514,f527,f534,f535,f542,f552,f561,f569,f585,f617,f620,f623,f664,f695,f703,f710,f779,f858,f865,f994,f1007,f1031,f1044,f1070,f1077,f1093,f1106,f1130,f1137,f1144,f1174,f1219,f1247,f1292,f1337,f1347,f1355,f1401,f1472,f1500,f1504,f1516,f1567,f1654,f1666,f1686,f1723,f1750,f1771,f1827,f1882,f2150,f2233,f2726,f3555,f3796,f3799,f3839,f3846,f3853,f3860,f4163,f4221,f4241,f4264,f4267,f4281,f4287,f4336,f4408,f4618,f4640])).

fof(f4640,plain,
    ( spl7_29
    | ~ spl7_82
    | ~ spl7_184
    | ~ spl7_186 ),
    inference(avatar_contradiction_clause,[],[f4639])).

fof(f4639,plain,
    ( $false
    | ~ spl7_29
    | ~ spl7_82
    | ~ spl7_184
    | ~ spl7_186 ),
    inference(subsumption_resolution,[],[f203,f4620])).

fof(f4620,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl7_82
    | ~ spl7_184
    | ~ spl7_186 ),
    inference(subsumption_resolution,[],[f4619,f4260])).

fof(f4260,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_186 ),
    inference(avatar_component_clause,[],[f4259])).

fof(f4259,plain,
    ( spl7_186
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_186])])).

fof(f4619,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ spl7_82
    | ~ spl7_184 ),
    inference(subsumption_resolution,[],[f4293,f607])).

fof(f607,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f606])).

fof(f606,plain,
    ( spl7_82
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f4293,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ spl7_184 ),
    inference(resolution,[],[f4240,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',symmetry_r1_tsep_1)).

fof(f4240,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl7_184 ),
    inference(avatar_component_clause,[],[f4239])).

fof(f4239,plain,
    ( spl7_184
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_184])])).

fof(f203,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl7_29
  <=> ~ r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f4618,plain,
    ( spl7_1
    | spl7_5
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_24
    | spl7_27
    | ~ spl7_80 ),
    inference(avatar_contradiction_clause,[],[f4617])).

fof(f4617,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4616,f127])).

fof(f127,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f4616,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4615,f162])).

fof(f162,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_16
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f4615,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4605,f190])).

fof(f190,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl7_24
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f4605,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_27
    | ~ spl7_80 ),
    inference(resolution,[],[f4456,f197])).

fof(f197,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl7_27
  <=> ~ r1_tsep_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f4456,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4455,f134])).

fof(f134,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_9
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f4455,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK4,X0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4454,f141])).

fof(f141,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f4454,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK4,X0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4453,f183])).

fof(f183,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_22
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f4453,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK4,X0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4448,f148])).

fof(f148,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f4448,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK4,X0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_80 ),
    inference(resolution,[],[f4278,f155])).

fof(f155,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_14
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f4278,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(sK4,X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(sK2,X4)
        | ~ v2_pre_topc(X4)
        | ~ m1_pre_topc(X5,sK2)
        | r1_tsep_1(sK4,X5)
        | v2_struct_0(X4) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4277,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f4277,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(sK2,X4)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,X4)
        | ~ m1_pre_topc(X5,sK2)
        | r1_tsep_1(sK4,X5)
        | v2_struct_0(X4) )
    | ~ spl7_5
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f4270,f120])).

fof(f120,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_5
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f4270,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X4)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,X4)
        | ~ m1_pre_topc(X5,sK2)
        | r1_tsep_1(sK4,X5)
        | v2_struct_0(X4) )
    | ~ spl7_80 ),
    inference(resolution,[],[f604,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tsep_1(X3,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t23_tmap_1)).

fof(f604,plain,
    ( r1_tsep_1(sK4,sK2)
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl7_80
  <=> r1_tsep_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f4408,plain,
    ( ~ spl7_191
    | spl7_3
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_60
    | spl7_63
    | spl7_73 ),
    inference(avatar_split_clause,[],[f4376,f537,f478,f472,f199,f182,f175,f147,f140,f133,f119,f112,f4406])).

fof(f4406,plain,
    ( spl7_191
  <=> ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_191])])).

fof(f112,plain,
    ( spl7_3
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f175,plain,
    ( spl7_20
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f199,plain,
    ( spl7_28
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f472,plain,
    ( spl7_60
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f478,plain,
    ( spl7_63
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f537,plain,
    ( spl7_73
  <=> ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f4376,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK3)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f4375,f479])).

fof(f479,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f478])).

fof(f4375,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK3)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_60
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f4358,f473])).

fof(f473,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f472])).

fof(f4358,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK3)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_73 ),
    inference(resolution,[],[f4302,f538])).

fof(f538,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f537])).

fof(f4302,plain,
    ( ! [X1] :
        ( r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X1) )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f4301,f134])).

fof(f4301,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f4300,f183])).

fof(f4300,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f4299,f141])).

fof(f4299,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f4295,f148])).

fof(f4295,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_20
    | ~ spl7_28 ),
    inference(resolution,[],[f4249,f176])).

fof(f176,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f4249,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(X0) )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f4248,f120])).

fof(f4248,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(X0) )
    | ~ spl7_3
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f4243,f113])).

fof(f113,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f4243,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,sK3)
        | r1_tsep_1(X1,sK2)
        | v2_struct_0(X0) )
    | ~ spl7_28 ),
    inference(resolution,[],[f200,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tsep_1(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f200,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f199])).

fof(f4336,plain,
    ( ~ spl7_189
    | spl7_49
    | spl7_75
    | ~ spl7_134
    | ~ spl7_136 ),
    inference(avatar_split_clause,[],[f4242,f1345,f1339,f544,f432,f4334])).

fof(f4334,plain,
    ( spl7_189
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).

fof(f432,plain,
    ( spl7_49
  <=> ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f544,plain,
    ( spl7_75
  <=> ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1339,plain,
    ( spl7_134
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f1345,plain,
    ( spl7_136
  <=> ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f4242,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_49
    | ~ spl7_75
    | ~ spl7_134
    | ~ spl7_136 ),
    inference(subsumption_resolution,[],[f1539,f545])).

fof(f545,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f544])).

fof(f1539,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_49
    | ~ spl7_134
    | ~ spl7_136 ),
    inference(subsumption_resolution,[],[f1538,f1340])).

fof(f1340,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | ~ spl7_134 ),
    inference(avatar_component_clause,[],[f1339])).

fof(f1538,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_49
    | ~ spl7_136 ),
    inference(resolution,[],[f433,f1346])).

fof(f1346,plain,
    ( ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_136 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f433,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f432])).

fof(f4287,plain,
    ( spl7_184
    | ~ spl7_187
    | ~ spl7_28
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f4256,f606,f199,f4262,f4239])).

fof(f4262,plain,
    ( spl7_187
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_187])])).

fof(f4256,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,sK2)
    | ~ spl7_28
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f4247,f607])).

fof(f4247,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2)
    | ~ spl7_28 ),
    inference(resolution,[],[f200,f86])).

fof(f4281,plain,
    ( spl7_34
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f1656,f612,f606,f603,f222])).

fof(f222,plain,
    ( spl7_34
  <=> r1_tsep_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f612,plain,
    ( spl7_84
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f1656,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_84 ),
    inference(subsumption_resolution,[],[f1655,f613])).

fof(f613,plain,
    ( l1_struct_0(sK4)
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f612])).

fof(f1655,plain,
    ( ~ l1_struct_0(sK4)
    | r1_tsep_1(sK2,sK4)
    | ~ spl7_80
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1537,f607])).

fof(f1537,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | r1_tsep_1(sK2,sK4)
    | ~ spl7_80 ),
    inference(resolution,[],[f604,f86])).

fof(f4267,plain,
    ( ~ spl7_40
    | spl7_187 ),
    inference(avatar_contradiction_clause,[],[f4266])).

fof(f4266,plain,
    ( $false
    | ~ spl7_40
    | ~ spl7_187 ),
    inference(subsumption_resolution,[],[f4265,f257])).

fof(f257,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl7_40
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f4265,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl7_187 ),
    inference(resolution,[],[f4263,f100])).

fof(f100,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',dt_l1_pre_topc)).

fof(f4263,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl7_187 ),
    inference(avatar_component_clause,[],[f4262])).

fof(f4264,plain,
    ( ~ spl7_187
    | ~ spl7_28
    | ~ spl7_82
    | spl7_185 ),
    inference(avatar_split_clause,[],[f4257,f4236,f606,f199,f4262])).

fof(f4236,plain,
    ( spl7_185
  <=> ~ r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_185])])).

fof(f4257,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl7_28
    | ~ spl7_82
    | ~ spl7_185 ),
    inference(subsumption_resolution,[],[f4256,f4237])).

fof(f4237,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ spl7_185 ),
    inference(avatar_component_clause,[],[f4236])).

fof(f4241,plain,
    ( spl7_184
    | spl7_1
    | spl7_3
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_96
    | ~ spl7_138 ),
    inference(avatar_split_clause,[],[f4183,f1399,f992,f182,f175,f168,f154,f147,f140,f133,f119,f112,f105,f4239])).

fof(f168,plain,
    ( spl7_18
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f992,plain,
    ( spl7_96
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f1399,plain,
    ( spl7_138
  <=> ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f4183,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_96
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4182,f169])).

fof(f169,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f4182,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_96
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4181,f176])).

fof(f4181,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_96
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4167,f113])).

fof(f4167,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_96
    | ~ spl7_138 ),
    inference(resolution,[],[f1442,f993])).

fof(f993,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f992])).

fof(f1442,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1441,f134])).

fof(f1441,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1440,f155])).

fof(f1440,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK4,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1439,f106])).

fof(f1439,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1438,f183])).

fof(f1438,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1437,f120])).

fof(f1437,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1436,f148])).

fof(f1436,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_10
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1435,f141])).

fof(f1435,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_138 ),
    inference(duplicate_literal_removal,[],[f1419])).

fof(f1419,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_138 ),
    inference(resolution,[],[f1400,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t34_tmap_1)).

fof(f1400,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl7_138 ),
    inference(avatar_component_clause,[],[f1399])).

fof(f4221,plain,
    ( spl7_1
    | spl7_3
    | spl7_5
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | spl7_27
    | ~ spl7_138 ),
    inference(avatar_contradiction_clause,[],[f4220])).

fof(f4220,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4219,f134])).

fof(f4219,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4218,f176])).

fof(f4218,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4217,f113])).

fof(f4217,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4216,f148])).

fof(f4216,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4215,f141])).

fof(f4215,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4214,f162])).

fof(f4214,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_27
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4213,f197])).

fof(f4213,plain,
    ( r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4212,f190])).

fof(f4212,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f4211,f127])).

fof(f4211,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(duplicate_literal_removal,[],[f4206])).

fof(f4206,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(resolution,[],[f1456,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t22_tsep_1)).

fof(f1456,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1455,f134])).

fof(f1455,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1454,f183])).

fof(f1454,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1453,f120])).

fof(f1453,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1452,f155])).

fof(f1452,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1451,f106])).

fof(f1451,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1450,f148])).

fof(f1450,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_10
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1433,f141])).

fof(f1433,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_138 ),
    inference(duplicate_literal_removal,[],[f1421])).

fof(f1421,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(sK4,X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_138 ),
    inference(resolution,[],[f1400,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4163,plain,
    ( spl7_182
    | spl7_1
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | spl7_75
    | ~ spl7_134
    | ~ spl7_174 ),
    inference(avatar_split_clause,[],[f3882,f3837,f1339,f544,f154,f147,f140,f133,f105,f4161])).

fof(f4161,plain,
    ( spl7_182
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_182])])).

fof(f3837,plain,
    ( spl7_174
  <=> k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK4) = k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).

fof(f3882,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_75
    | ~ spl7_134
    | ~ spl7_174 ),
    inference(subsumption_resolution,[],[f3881,f134])).

fof(f3881,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)))
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_75
    | ~ spl7_134
    | ~ spl7_174 ),
    inference(subsumption_resolution,[],[f3880,f155])).

fof(f3880,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_75
    | ~ spl7_134
    | ~ spl7_174 ),
    inference(subsumption_resolution,[],[f3879,f106])).

fof(f3879,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_75
    | ~ spl7_134
    | ~ spl7_174 ),
    inference(subsumption_resolution,[],[f3878,f1340])).

fof(f3878,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_75
    | ~ spl7_174 ),
    inference(subsumption_resolution,[],[f3877,f545])).

fof(f3877,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)))
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_174 ),
    inference(subsumption_resolution,[],[f3876,f148])).

fof(f3876,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_174 ),
    inference(subsumption_resolution,[],[f3868,f141])).

fof(f3868,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_174 ),
    inference(superposition,[],[f78,f3838])).

fof(f3838,plain,
    ( k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK4) = k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_174 ),
    inference(avatar_component_clause,[],[f3837])).

fof(f3860,plain,
    ( spl7_180
    | spl7_7
    | spl7_9
    | ~ spl7_12
    | ~ spl7_24
    | spl7_75
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f1368,f1339,f544,f189,f147,f133,f126,f3858])).

fof(f3858,plain,
    ( spl7_180
  <=> k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK1) = k1_tsep_1(sK0,sK1,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_180])])).

fof(f1368,plain,
    ( k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK1) = k1_tsep_1(sK0,sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_75
    | ~ spl7_134 ),
    inference(subsumption_resolution,[],[f1359,f545])).

fof(f1359,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK1) = k1_tsep_1(sK0,sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_134 ),
    inference(resolution,[],[f1340,f294])).

fof(f294,plain,
    ( ! [X13] :
        ( ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(X13)
        | k1_tsep_1(sK0,X13,sK1) = k1_tsep_1(sK0,sK1,X13) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f293,f134])).

fof(f293,plain,
    ( ! [X13] :
        ( v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X13,sK1) = k1_tsep_1(sK0,sK1,X13) )
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f292,f127])).

fof(f292,plain,
    ( ! [X13] :
        ( v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X13,sK1) = k1_tsep_1(sK0,sK1,X13) )
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f275,f148])).

fof(f275,plain,
    ( ! [X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X13,sK1) = k1_tsep_1(sK0,sK1,X13) )
    | ~ spl7_24 ),
    inference(resolution,[],[f77,f190])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | v2_struct_0(X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',commutativity_k1_tsep_1)).

fof(f3853,plain,
    ( spl7_178
    | spl7_5
    | spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | spl7_75
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f1367,f1339,f544,f182,f147,f133,f119,f3851])).

fof(f3851,plain,
    ( spl7_178
  <=> k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK2) = k1_tsep_1(sK0,sK2,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).

fof(f1367,plain,
    ( k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK2) = k1_tsep_1(sK0,sK2,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_75
    | ~ spl7_134 ),
    inference(subsumption_resolution,[],[f1358,f545])).

fof(f1358,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK2) = k1_tsep_1(sK0,sK2,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_134 ),
    inference(resolution,[],[f1340,f297])).

fof(f297,plain,
    ( ! [X14] :
        ( ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(X14)
        | k1_tsep_1(sK0,X14,sK2) = k1_tsep_1(sK0,sK2,X14) )
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f296,f134])).

fof(f296,plain,
    ( ! [X14] :
        ( v2_struct_0(X14)
        | ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X14,sK2) = k1_tsep_1(sK0,sK2,X14) )
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f295,f120])).

fof(f295,plain,
    ( ! [X14] :
        ( v2_struct_0(X14)
        | ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(sK2)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X14,sK2) = k1_tsep_1(sK0,sK2,X14) )
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f276,f148])).

fof(f276,plain,
    ( ! [X14] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(sK2)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X14,sK2) = k1_tsep_1(sK0,sK2,X14) )
    | ~ spl7_22 ),
    inference(resolution,[],[f77,f183])).

fof(f3846,plain,
    ( spl7_176
    | spl7_3
    | spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | spl7_75
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f1366,f1339,f544,f175,f147,f133,f112,f3844])).

fof(f3844,plain,
    ( spl7_176
  <=> k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK3) = k1_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_176])])).

fof(f1366,plain,
    ( k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK3) = k1_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_75
    | ~ spl7_134 ),
    inference(subsumption_resolution,[],[f1357,f545])).

fof(f1357,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK3) = k1_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_134 ),
    inference(resolution,[],[f1340,f303])).

fof(f303,plain,
    ( ! [X16] :
        ( ~ m1_pre_topc(X16,sK0)
        | v2_struct_0(X16)
        | k1_tsep_1(sK0,X16,sK3) = k1_tsep_1(sK0,sK3,X16) )
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f302,f134])).

fof(f302,plain,
    ( ! [X16] :
        ( v2_struct_0(X16)
        | ~ m1_pre_topc(X16,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X16,sK3) = k1_tsep_1(sK0,sK3,X16) )
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f301,f113])).

fof(f301,plain,
    ( ! [X16] :
        ( v2_struct_0(X16)
        | ~ m1_pre_topc(X16,sK0)
        | v2_struct_0(sK3)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X16,sK3) = k1_tsep_1(sK0,sK3,X16) )
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f278,f148])).

fof(f278,plain,
    ( ! [X16] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,sK0)
        | v2_struct_0(sK3)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X16,sK3) = k1_tsep_1(sK0,sK3,X16) )
    | ~ spl7_20 ),
    inference(resolution,[],[f77,f176])).

fof(f3839,plain,
    ( spl7_174
    | spl7_1
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | spl7_75
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f1365,f1339,f544,f154,f147,f133,f105,f3837])).

fof(f1365,plain,
    ( k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK4) = k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_75
    | ~ spl7_134 ),
    inference(subsumption_resolution,[],[f1356,f545])).

fof(f1356,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | k1_tsep_1(sK0,k2_tsep_1(sK0,sK2,sK4),sK4) = k1_tsep_1(sK0,sK4,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_134 ),
    inference(resolution,[],[f1340,f306])).

fof(f306,plain,
    ( ! [X17] :
        ( ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(X17)
        | k1_tsep_1(sK0,X17,sK4) = k1_tsep_1(sK0,sK4,X17) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f305,f134])).

fof(f305,plain,
    ( ! [X17] :
        ( v2_struct_0(X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X17,sK4) = k1_tsep_1(sK0,sK4,X17) )
    | ~ spl7_1
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f304,f106])).

fof(f304,plain,
    ( ! [X17] :
        ( v2_struct_0(X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(sK4)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X17,sK4) = k1_tsep_1(sK0,sK4,X17) )
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f279,f148])).

fof(f279,plain,
    ( ! [X17] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(sK4)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X17,sK4) = k1_tsep_1(sK0,sK4,X17) )
    | ~ spl7_14 ),
    inference(resolution,[],[f77,f155])).

fof(f3799,plain,
    ( ~ spl7_12
    | spl7_171 ),
    inference(avatar_contradiction_clause,[],[f3798])).

fof(f3798,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_171 ),
    inference(subsumption_resolution,[],[f3797,f148])).

fof(f3797,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_171 ),
    inference(resolution,[],[f3789,f95])).

fof(f95,plain,(
    ! [X0] :
      ( m1_pre_topc(sK5(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',existence_m1_pre_topc)).

fof(f3789,plain,
    ( ~ m1_pre_topc(sK5(sK0),sK0)
    | ~ spl7_171 ),
    inference(avatar_component_clause,[],[f3788])).

fof(f3788,plain,
    ( spl7_171
  <=> ~ m1_pre_topc(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_171])])).

fof(f3796,plain,
    ( ~ spl7_171
    | spl7_106
    | spl7_172
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f1080,f1036,f189,f147,f140,f133,f126,f3794,f1042,f3788])).

fof(f1042,plain,
    ( spl7_106
  <=> v2_struct_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f3794,plain,
    ( spl7_172
  <=> m1_pre_topc(sK5(sK0),k1_tsep_1(sK0,sK1,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f1036,plain,
    ( spl7_104
  <=> k1_tsep_1(sK0,sK1,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f1080,plain,
    ( m1_pre_topc(sK5(sK0),k1_tsep_1(sK0,sK1,sK5(sK0)))
    | v2_struct_0(sK5(sK0))
    | ~ m1_pre_topc(sK5(sK0),sK0)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1079,f134])).

fof(f1079,plain,
    ( m1_pre_topc(sK5(sK0),k1_tsep_1(sK0,sK1,sK5(sK0)))
    | v2_struct_0(sK5(sK0))
    | ~ m1_pre_topc(sK5(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1078,f190])).

fof(f1078,plain,
    ( m1_pre_topc(sK5(sK0),k1_tsep_1(sK0,sK1,sK5(sK0)))
    | v2_struct_0(sK5(sK0))
    | ~ m1_pre_topc(sK5(sK0),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1059,f127])).

fof(f1059,plain,
    ( m1_pre_topc(sK5(sK0),k1_tsep_1(sK0,sK1,sK5(sK0)))
    | v2_struct_0(sK5(sK0))
    | ~ m1_pre_topc(sK5(sK0),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1058,f148])).

fof(f1058,plain,
    ( m1_pre_topc(sK5(sK0),k1_tsep_1(sK0,sK1,sK5(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0))
    | ~ m1_pre_topc(sK5(sK0),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1047,f141])).

fof(f1047,plain,
    ( m1_pre_topc(sK5(sK0),k1_tsep_1(sK0,sK1,sK5(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0))
    | ~ m1_pre_topc(sK5(sK0),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_104 ),
    inference(superposition,[],[f78,f1037])).

fof(f1037,plain,
    ( k1_tsep_1(sK0,sK1,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK1)
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f3555,plain,
    ( ~ spl7_42
    | spl7_165 ),
    inference(avatar_contradiction_clause,[],[f3554])).

fof(f3554,plain,
    ( $false
    | ~ spl7_42
    | ~ spl7_165 ),
    inference(subsumption_resolution,[],[f3553,f268])).

fof(f268,plain,
    ( l1_pre_topc(sK4)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl7_42
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f3553,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl7_165 ),
    inference(resolution,[],[f2713,f95])).

fof(f2713,plain,
    ( ~ m1_pre_topc(sK5(sK4),sK4)
    | ~ spl7_165 ),
    inference(avatar_component_clause,[],[f2712])).

fof(f2712,plain,
    ( spl7_165
  <=> ~ m1_pre_topc(sK5(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_165])])).

fof(f2726,plain,
    ( ~ spl7_165
    | ~ spl7_167
    | spl7_168
    | spl7_1
    | spl7_3
    | ~ spl7_18
    | ~ spl7_42
    | ~ spl7_114
    | spl7_117 ),
    inference(avatar_split_clause,[],[f1123,f1101,f1098,f267,f168,f112,f105,f2724,f2718,f2712])).

fof(f2718,plain,
    ( spl7_167
  <=> ~ v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_167])])).

fof(f2724,plain,
    ( spl7_168
  <=> m1_pre_topc(sK5(sK4),k1_tsep_1(sK4,sK3,sK5(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f1098,plain,
    ( spl7_114
  <=> k1_tsep_1(sK4,sK3,sK5(sK4)) = k1_tsep_1(sK4,sK5(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f1101,plain,
    ( spl7_117
  <=> ~ v2_struct_0(sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f1123,plain,
    ( m1_pre_topc(sK5(sK4),k1_tsep_1(sK4,sK3,sK5(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ m1_pre_topc(sK5(sK4),sK4)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_18
    | ~ spl7_42
    | ~ spl7_114
    | ~ spl7_117 ),
    inference(subsumption_resolution,[],[f1122,f106])).

fof(f1122,plain,
    ( m1_pre_topc(sK5(sK4),k1_tsep_1(sK4,sK3,sK5(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ m1_pre_topc(sK5(sK4),sK4)
    | v2_struct_0(sK4)
    | ~ spl7_3
    | ~ spl7_18
    | ~ spl7_42
    | ~ spl7_114
    | ~ spl7_117 ),
    inference(subsumption_resolution,[],[f1121,f169])).

fof(f1121,plain,
    ( m1_pre_topc(sK5(sK4),k1_tsep_1(sK4,sK3,sK5(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ m1_pre_topc(sK5(sK4),sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | ~ spl7_3
    | ~ spl7_42
    | ~ spl7_114
    | ~ spl7_117 ),
    inference(subsumption_resolution,[],[f1120,f113])).

fof(f1120,plain,
    ( m1_pre_topc(sK5(sK4),k1_tsep_1(sK4,sK3,sK5(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ m1_pre_topc(sK5(sK4),sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | ~ spl7_42
    | ~ spl7_114
    | ~ spl7_117 ),
    inference(subsumption_resolution,[],[f1119,f1102])).

fof(f1102,plain,
    ( ~ v2_struct_0(sK5(sK4))
    | ~ spl7_117 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f1119,plain,
    ( m1_pre_topc(sK5(sK4),k1_tsep_1(sK4,sK3,sK5(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK5(sK4))
    | ~ m1_pre_topc(sK5(sK4),sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | ~ spl7_42
    | ~ spl7_114 ),
    inference(subsumption_resolution,[],[f1109,f268])).

fof(f1109,plain,
    ( m1_pre_topc(sK5(sK4),k1_tsep_1(sK4,sK3,sK5(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK5(sK4))
    | ~ m1_pre_topc(sK5(sK4),sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | ~ spl7_114 ),
    inference(superposition,[],[f78,f1099])).

fof(f1099,plain,
    ( k1_tsep_1(sK4,sK3,sK5(sK4)) = k1_tsep_1(sK4,sK5(sK4),sK3)
    | ~ spl7_114 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f2233,plain,
    ( ~ spl7_38
    | spl7_159 ),
    inference(avatar_contradiction_clause,[],[f2232])).

fof(f2232,plain,
    ( $false
    | ~ spl7_38
    | ~ spl7_159 ),
    inference(subsumption_resolution,[],[f2231,f250])).

fof(f250,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl7_38
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f2231,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl7_159 ),
    inference(resolution,[],[f2137,f95])).

fof(f2137,plain,
    ( ~ m1_pre_topc(sK5(sK2),sK2)
    | ~ spl7_159 ),
    inference(avatar_component_clause,[],[f2136])).

fof(f2136,plain,
    ( spl7_159
  <=> ~ m1_pre_topc(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_159])])).

fof(f2150,plain,
    ( ~ spl7_159
    | ~ spl7_161
    | spl7_162
    | spl7_5
    | spl7_7
    | ~ spl7_16
    | ~ spl7_38
    | ~ spl7_98
    | spl7_101 ),
    inference(avatar_split_clause,[],[f1024,f1002,f999,f249,f161,f126,f119,f2148,f2142,f2136])).

fof(f2142,plain,
    ( spl7_161
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_161])])).

fof(f2148,plain,
    ( spl7_162
  <=> m1_pre_topc(sK5(sK2),k1_tsep_1(sK2,sK1,sK5(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f999,plain,
    ( spl7_98
  <=> k1_tsep_1(sK2,sK1,sK5(sK2)) = k1_tsep_1(sK2,sK5(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f1002,plain,
    ( spl7_101
  <=> ~ v2_struct_0(sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f1024,plain,
    ( m1_pre_topc(sK5(sK2),k1_tsep_1(sK2,sK1,sK5(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ m1_pre_topc(sK5(sK2),sK2)
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_38
    | ~ spl7_98
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f1023,f120])).

fof(f1023,plain,
    ( m1_pre_topc(sK5(sK2),k1_tsep_1(sK2,sK1,sK5(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ m1_pre_topc(sK5(sK2),sK2)
    | v2_struct_0(sK2)
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_38
    | ~ spl7_98
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f1022,f162])).

fof(f1022,plain,
    ( m1_pre_topc(sK5(sK2),k1_tsep_1(sK2,sK1,sK5(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ m1_pre_topc(sK5(sK2),sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | ~ spl7_7
    | ~ spl7_38
    | ~ spl7_98
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f1021,f127])).

fof(f1021,plain,
    ( m1_pre_topc(sK5(sK2),k1_tsep_1(sK2,sK1,sK5(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ m1_pre_topc(sK5(sK2),sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | ~ spl7_38
    | ~ spl7_98
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f1020,f1003])).

fof(f1003,plain,
    ( ~ v2_struct_0(sK5(sK2))
    | ~ spl7_101 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f1020,plain,
    ( m1_pre_topc(sK5(sK2),k1_tsep_1(sK2,sK1,sK5(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK5(sK2))
    | ~ m1_pre_topc(sK5(sK2),sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | ~ spl7_38
    | ~ spl7_98 ),
    inference(subsumption_resolution,[],[f1010,f250])).

fof(f1010,plain,
    ( m1_pre_topc(sK5(sK2),k1_tsep_1(sK2,sK1,sK5(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5(sK2))
    | ~ m1_pre_topc(sK5(sK2),sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | ~ spl7_98 ),
    inference(superposition,[],[f78,f1000])).

fof(f1000,plain,
    ( k1_tsep_1(sK2,sK1,sK5(sK2)) = k1_tsep_1(sK2,sK5(sK2),sK1)
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f999])).

fof(f1882,plain,
    ( spl7_156
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_60
    | spl7_63
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f1313,f1290,f478,f472,f189,f147,f140,f133,f126,f1880])).

fof(f1880,plain,
    ( spl7_156
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f1290,plain,
    ( spl7_130
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f1313,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)))
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f1312,f134])).

fof(f1312,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(sK0)
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f1311,f190])).

fof(f1311,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f1310,f127])).

fof(f1310,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f1309,f473])).

fof(f1309,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_63
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f1308,f479])).

fof(f1308,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f1307,f148])).

fof(f1307,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f1295,f141])).

fof(f1295,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_130 ),
    inference(superposition,[],[f78,f1291])).

fof(f1291,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f1290])).

fof(f1827,plain,
    ( spl7_154
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_60
    | spl7_63
    | ~ spl7_128 ),
    inference(avatar_split_clause,[],[f1285,f1245,f478,f472,f182,f147,f140,f133,f119,f1825])).

fof(f1825,plain,
    ( spl7_154
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f1245,plain,
    ( spl7_128
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f1285,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)))
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f1284,f134])).

fof(f1284,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f1283,f183])).

fof(f1283,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f1282,f120])).

fof(f1282,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f1281,f473])).

fof(f1281,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_63
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f1280,f479])).

fof(f1280,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f1279,f148])).

fof(f1279,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f1267,f141])).

fof(f1267,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_128 ),
    inference(superposition,[],[f78,f1246])).

fof(f1246,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_128 ),
    inference(avatar_component_clause,[],[f1245])).

fof(f1771,plain,
    ( spl7_152
    | spl7_3
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_60
    | spl7_63
    | ~ spl7_126 ),
    inference(avatar_split_clause,[],[f1240,f1217,f478,f472,f175,f147,f140,f133,f112,f1769])).

fof(f1769,plain,
    ( spl7_152
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f1217,plain,
    ( spl7_126
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK3) = k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f1240,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_126 ),
    inference(subsumption_resolution,[],[f1239,f134])).

fof(f1239,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_126 ),
    inference(subsumption_resolution,[],[f1238,f176])).

fof(f1238,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_126 ),
    inference(subsumption_resolution,[],[f1237,f113])).

fof(f1237,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_126 ),
    inference(subsumption_resolution,[],[f1236,f473])).

fof(f1236,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_63
    | ~ spl7_126 ),
    inference(subsumption_resolution,[],[f1235,f479])).

fof(f1235,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_126 ),
    inference(subsumption_resolution,[],[f1234,f148])).

fof(f1234,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_126 ),
    inference(subsumption_resolution,[],[f1222,f141])).

fof(f1222,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_126 ),
    inference(superposition,[],[f78,f1218])).

fof(f1218,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK3) = k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_126 ),
    inference(avatar_component_clause,[],[f1217])).

fof(f1750,plain,
    ( spl7_62
    | spl7_150
    | spl7_9
    | ~ spl7_12
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f553,f472,f147,f133,f1748,f481])).

fof(f481,plain,
    ( spl7_62
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f1748,plain,
    ( spl7_150
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | k1_tsep_1(sK0,X0,k1_tsep_1(sK0,sK1,sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f553,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | k1_tsep_1(sK0,X0,k1_tsep_1(sK0,sK1,sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0) )
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f509,f134])).

fof(f509,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,k1_tsep_1(sK0,sK1,sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0) )
    | ~ spl7_12
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f503,f148])).

fof(f503,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,k1_tsep_1(sK0,sK1,sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0) )
    | ~ spl7_60 ),
    inference(resolution,[],[f473,f77])).

fof(f1723,plain,
    ( spl7_148
    | spl7_1
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_60
    | spl7_63
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f1195,f1172,f478,f472,f154,f147,f140,f133,f105,f1721])).

fof(f1721,plain,
    ( spl7_148
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f1172,plain,
    ( spl7_124
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK4) = k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f1195,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f1194,f134])).

fof(f1194,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f1193,f155])).

fof(f1193,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f1192,f106])).

fof(f1192,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f1191,f473])).

fof(f1191,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_63
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f1190,f479])).

fof(f1190,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f1189,f148])).

fof(f1189,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f1177,f141])).

fof(f1177,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_124 ),
    inference(superposition,[],[f78,f1173])).

fof(f1173,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK4) = k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f1172])).

fof(f1686,plain,
    ( spl7_32
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f1506,f444,f438,f435,f216])).

fof(f216,plain,
    ( spl7_32
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f435,plain,
    ( spl7_48
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f438,plain,
    ( spl7_50
  <=> l1_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f444,plain,
    ( spl7_52
  <=> l1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f1506,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f1505,f445])).

fof(f445,plain,
    ( l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f444])).

fof(f1505,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_48
    | ~ spl7_50 ),
    inference(subsumption_resolution,[],[f709,f439])).

fof(f439,plain,
    ( l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f438])).

fof(f709,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_48 ),
    inference(resolution,[],[f436,f86])).

fof(f436,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f435])).

fof(f1666,plain,
    ( spl7_35
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_84 ),
    inference(avatar_contradiction_clause,[],[f1665])).

fof(f1665,plain,
    ( $false
    | ~ spl7_35
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_84 ),
    inference(subsumption_resolution,[],[f220,f1656])).

fof(f220,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl7_35
  <=> ~ r1_tsep_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1654,plain,
    ( spl7_1
    | spl7_3
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_22
    | spl7_29
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f1653])).

fof(f1653,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_29
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1652,f113])).

fof(f1652,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_29
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1651,f169])).

fof(f1651,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK3)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_29
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1640,f176])).

fof(f1640,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK3)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_29
    | ~ spl7_34 ),
    inference(resolution,[],[f1576,f203])).

fof(f1576,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1575,f134])).

fof(f1575,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1574,f183])).

fof(f1574,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1573,f141])).

fof(f1573,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1568,f148])).

fof(f1568,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_34 ),
    inference(resolution,[],[f1527,f155])).

fof(f1527,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(sK4,X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ v2_pre_topc(X4)
        | ~ m1_pre_topc(sK2,X4)
        | ~ m1_pre_topc(X5,sK4)
        | r1_tsep_1(sK2,X5)
        | v2_struct_0(X4) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1526,f120])).

fof(f1526,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X4)
        | ~ m1_pre_topc(X5,sK4)
        | r1_tsep_1(sK2,X5)
        | v2_struct_0(X4) )
    | ~ spl7_1
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1519,f106])).

fof(f1519,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X4)
        | ~ m1_pre_topc(X5,sK4)
        | r1_tsep_1(sK2,X5)
        | v2_struct_0(X4) )
    | ~ spl7_34 ),
    inference(resolution,[],[f223,f88])).

fof(f223,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f222])).

fof(f1567,plain,
    ( ~ spl7_147
    | spl7_1
    | ~ spl7_14
    | spl7_71
    | ~ spl7_136 ),
    inference(avatar_split_clause,[],[f1392,f1345,f529,f154,f105,f1565])).

fof(f1565,plain,
    ( spl7_147
  <=> ~ m1_pre_topc(sK4,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_147])])).

fof(f529,plain,
    ( spl7_71
  <=> ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f1392,plain,
    ( ~ m1_pre_topc(sK4,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_1
    | ~ spl7_14
    | ~ spl7_71
    | ~ spl7_136 ),
    inference(subsumption_resolution,[],[f1391,f106])).

fof(f1391,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_14
    | ~ spl7_71
    | ~ spl7_136 ),
    inference(subsumption_resolution,[],[f1379,f155])).

fof(f1379,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_71
    | ~ spl7_136 ),
    inference(resolution,[],[f1346,f530])).

fof(f530,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f529])).

fof(f1516,plain,
    ( spl7_33
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52 ),
    inference(avatar_contradiction_clause,[],[f1515])).

fof(f1515,plain,
    ( $false
    | ~ spl7_33
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f214,f1506])).

fof(f214,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_33
  <=> ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f1504,plain,
    ( ~ spl7_135
    | spl7_144
    | spl7_3
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_32
    | spl7_63
    | spl7_75 ),
    inference(avatar_split_clause,[],[f687,f544,f478,f216,f189,f175,f147,f140,f133,f126,f112,f1502,f1342])).

fof(f1342,plain,
    ( spl7_135
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f1502,plain,
    ( spl7_144
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f687,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f686,f176])).

fof(f686,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f685,f113])).

fof(f685,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f684,f190])).

fof(f684,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f683,f127])).

fof(f683,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f682,f134])).

fof(f682,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f681,f141])).

fof(f681,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f680,f148])).

fof(f680,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(duplicate_literal_removal,[],[f677])).

fof(f677,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(resolution,[],[f640,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',dt_k1_tsep_1)).

fof(f640,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ v2_pre_topc(X2)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X2) )
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f639,f479])).

fof(f639,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X2)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X2) )
    | ~ spl7_32
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f633,f545])).

fof(f633,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X2)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X2) )
    | ~ spl7_32 ),
    inference(resolution,[],[f217,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tsep_1(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f217,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1500,plain,
    ( ~ spl7_143
    | spl7_5
    | ~ spl7_22
    | spl7_73
    | ~ spl7_136 ),
    inference(avatar_split_clause,[],[f1390,f1345,f537,f182,f119,f1498])).

fof(f1498,plain,
    ( spl7_143
  <=> ~ m1_pre_topc(sK2,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).

fof(f1390,plain,
    ( ~ m1_pre_topc(sK2,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_5
    | ~ spl7_22
    | ~ spl7_73
    | ~ spl7_136 ),
    inference(subsumption_resolution,[],[f1389,f120])).

fof(f1389,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_22
    | ~ spl7_73
    | ~ spl7_136 ),
    inference(subsumption_resolution,[],[f1378,f183])).

fof(f1378,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_73
    | ~ spl7_136 ),
    inference(resolution,[],[f1346,f538])).

fof(f1472,plain,
    ( ~ spl7_135
    | spl7_140
    | spl7_3
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_32
    | spl7_63
    | spl7_75 ),
    inference(avatar_split_clause,[],[f675,f544,f478,f216,f189,f175,f147,f140,f133,f126,f112,f1470,f1342])).

fof(f1470,plain,
    ( spl7_140
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f675,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f674,f176])).

fof(f674,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f673,f113])).

fof(f673,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f672,f190])).

fof(f672,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f671,f127])).

fof(f671,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f670,f134])).

fof(f670,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f669,f141])).

fof(f669,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f668,f148])).

fof(f668,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(duplicate_literal_removal,[],[f665])).

fof(f665,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(resolution,[],[f638,f76])).

fof(f638,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0) )
    | ~ spl7_32
    | ~ spl7_63
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f637,f545])).

fof(f637,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0) )
    | ~ spl7_32
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f632,f479])).

fof(f632,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0) )
    | ~ spl7_32 ),
    inference(resolution,[],[f217,f90])).

fof(f1401,plain,
    ( ~ spl7_135
    | spl7_138
    | spl7_3
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f656,f583,f189,f175,f147,f140,f133,f126,f112,f1399,f1342])).

fof(f583,plain,
    ( spl7_78
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f656,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f655,f176])).

fof(f655,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f654,f113])).

fof(f654,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f653,f190])).

fof(f653,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f652,f127])).

fof(f652,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f651,f148])).

fof(f651,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f650,f141])).

fof(f650,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_9
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f649,f134])).

fof(f649,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_78 ),
    inference(duplicate_literal_removal,[],[f646])).

fof(f646,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_78 ),
    inference(resolution,[],[f584,f76])).

fof(f584,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | v2_struct_0(X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f583])).

fof(f1355,plain,
    ( spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | spl7_135 ),
    inference(avatar_contradiction_clause,[],[f1354])).

fof(f1354,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_135 ),
    inference(subsumption_resolution,[],[f1353,f134])).

fof(f1353,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_135 ),
    inference(subsumption_resolution,[],[f1352,f155])).

fof(f1352,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_135 ),
    inference(subsumption_resolution,[],[f1351,f106])).

fof(f1351,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_135 ),
    inference(subsumption_resolution,[],[f1350,f183])).

fof(f1350,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_135 ),
    inference(subsumption_resolution,[],[f1349,f120])).

fof(f1349,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_12
    | ~ spl7_135 ),
    inference(subsumption_resolution,[],[f1348,f148])).

fof(f1348,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_135 ),
    inference(resolution,[],[f1343,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',dt_k2_tsep_1)).

fof(f1343,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | ~ spl7_135 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1347,plain,
    ( ~ spl7_135
    | spl7_136
    | spl7_3
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_76 ),
    inference(avatar_split_clause,[],[f627,f550,f189,f175,f147,f140,f133,f126,f112,f1345,f1342])).

fof(f550,plain,
    ( spl7_76
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f627,plain,
    ( ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f626,f176])).

fof(f626,plain,
    ( ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f625,f113])).

fof(f625,plain,
    ( ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f624,f190])).

fof(f624,plain,
    ( ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f576,f127])).

fof(f576,plain,
    ( ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f575,f148])).

fof(f575,plain,
    ( ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f574,f141])).

fof(f574,plain,
    ( ! [X0] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_9
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f573,f134])).

fof(f573,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_76 ),
    inference(duplicate_literal_removal,[],[f570])).

fof(f570,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_76 ),
    inference(resolution,[],[f551,f76])).

fof(f551,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | v2_struct_0(X0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f550])).

fof(f1337,plain,
    ( spl7_132
    | spl7_106
    | spl7_9
    | ~ spl7_12
    | ~ spl7_60
    | spl7_63 ),
    inference(avatar_split_clause,[],[f732,f478,f472,f147,f133,f1042,f1335])).

fof(f1335,plain,
    ( spl7_132
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f732,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f731,f134])).

fof(f731,plain,
    ( v2_struct_0(sK5(sK0))
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f730,f148])).

fof(f730,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0))
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_60
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f714,f479])).

fof(f714,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0))
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_60 ),
    inference(resolution,[],[f281,f473])).

fof(f281,plain,(
    ! [X19,X18] :
      ( ~ m1_pre_topc(X19,X18)
      | v2_struct_0(X19)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(sK5(X18))
      | v2_struct_0(X18)
      | k1_tsep_1(X18,X19,sK5(X18)) = k1_tsep_1(X18,sK5(X18),X19) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X19,X18] :
      ( ~ l1_pre_topc(X18)
      | v2_struct_0(X19)
      | ~ m1_pre_topc(X19,X18)
      | v2_struct_0(sK5(X18))
      | v2_struct_0(X18)
      | k1_tsep_1(X18,X19,sK5(X18)) = k1_tsep_1(X18,sK5(X18),X19)
      | ~ l1_pre_topc(X18) ) ),
    inference(resolution,[],[f77,f95])).

fof(f1292,plain,
    ( spl7_130
    | spl7_62
    | spl7_7
    | spl7_9
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f502,f472,f189,f147,f133,f126,f481,f1290])).

fof(f502,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_60 ),
    inference(resolution,[],[f473,f294])).

fof(f1247,plain,
    ( spl7_128
    | spl7_62
    | spl7_5
    | spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f501,f472,f182,f147,f133,f119,f481,f1245])).

fof(f501,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_60 ),
    inference(resolution,[],[f473,f297])).

fof(f1219,plain,
    ( spl7_126
    | spl7_62
    | spl7_3
    | spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f500,f472,f175,f147,f133,f112,f481,f1217])).

fof(f500,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK3) = k1_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_60 ),
    inference(resolution,[],[f473,f303])).

fof(f1174,plain,
    ( spl7_124
    | spl7_62
    | spl7_1
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f499,f472,f154,f147,f133,f105,f481,f1172])).

fof(f499,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK4) = k1_tsep_1(sK0,sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_60 ),
    inference(resolution,[],[f473,f306])).

fof(f1144,plain,
    ( spl7_122
    | spl7_106
    | spl7_1
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f423,f154,f147,f133,f105,f1042,f1142])).

fof(f1142,plain,
    ( spl7_122
  <=> k1_tsep_1(sK0,sK4,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f423,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,sK4,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK4)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f418,f148])).

fof(f418,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,sK4,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK4)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(resolution,[],[f306,f95])).

fof(f1137,plain,
    ( spl7_120
    | spl7_106
    | spl7_3
    | spl7_9
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f411,f175,f147,f133,f112,f1042,f1135])).

fof(f1135,plain,
    ( spl7_120
  <=> k1_tsep_1(sK0,sK3,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f411,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,sK3,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK3)
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f405,f148])).

fof(f405,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,sK3,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(resolution,[],[f303,f95])).

fof(f1130,plain,
    ( spl7_118
    | spl7_1
    | spl7_3
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_94 ),
    inference(avatar_split_clause,[],[f987,f863,f175,f154,f147,f140,f133,f112,f105,f1128])).

fof(f1128,plain,
    ( spl7_118
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f863,plain,
    ( spl7_94
  <=> k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f987,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f986,f134])).

fof(f986,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f985,f176])).

fof(f985,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f984,f113])).

fof(f984,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f983,f155])).

fof(f983,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f982,f106])).

fof(f982,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f981,f148])).

fof(f981,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f969,f141])).

fof(f969,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_94 ),
    inference(superposition,[],[f78,f864])).

fof(f864,plain,
    ( k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f863])).

fof(f1106,plain,
    ( spl7_114
    | spl7_116
    | spl7_1
    | spl7_3
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f398,f267,f168,f112,f105,f1104,f1098])).

fof(f1104,plain,
    ( spl7_116
  <=> v2_struct_0(sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f398,plain,
    ( v2_struct_0(sK5(sK4))
    | k1_tsep_1(sK4,sK3,sK5(sK4)) = k1_tsep_1(sK4,sK5(sK4),sK3)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f393,f268])).

fof(f393,plain,
    ( v2_struct_0(sK5(sK4))
    | k1_tsep_1(sK4,sK3,sK5(sK4)) = k1_tsep_1(sK4,sK5(sK4),sK3)
    | ~ l1_pre_topc(sK4)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(resolution,[],[f300,f95])).

fof(f300,plain,
    ( ! [X15] :
        ( ~ m1_pre_topc(X15,sK4)
        | v2_struct_0(X15)
        | k1_tsep_1(sK4,X15,sK3) = k1_tsep_1(sK4,sK3,X15) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f299,f106])).

fof(f299,plain,
    ( ! [X15] :
        ( v2_struct_0(X15)
        | ~ m1_pre_topc(X15,sK4)
        | v2_struct_0(sK4)
        | k1_tsep_1(sK4,X15,sK3) = k1_tsep_1(sK4,sK3,X15) )
    | ~ spl7_3
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f298,f113])).

fof(f298,plain,
    ( ! [X15] :
        ( v2_struct_0(X15)
        | ~ m1_pre_topc(X15,sK4)
        | v2_struct_0(sK3)
        | v2_struct_0(sK4)
        | k1_tsep_1(sK4,X15,sK3) = k1_tsep_1(sK4,sK3,X15) )
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f277,f268])).

fof(f277,plain,
    ( ! [X15] :
        ( ~ l1_pre_topc(sK4)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,sK4)
        | v2_struct_0(sK3)
        | v2_struct_0(sK4)
        | k1_tsep_1(sK4,X15,sK3) = k1_tsep_1(sK4,sK3,X15) )
    | ~ spl7_18 ),
    inference(resolution,[],[f77,f169])).

fof(f1093,plain,
    ( spl7_112
    | spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f966,f777,f182,f154,f147,f140,f133,f119,f105,f1091])).

fof(f1091,plain,
    ( spl7_112
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f777,plain,
    ( spl7_90
  <=> k1_tsep_1(sK0,sK2,sK4) = k1_tsep_1(sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f966,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f965,f134])).

fof(f965,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f964,f183])).

fof(f964,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f963,f120])).

fof(f963,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f962,f155])).

fof(f962,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f961,f106])).

fof(f961,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f960,f148])).

fof(f960,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f948,f141])).

fof(f948,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_90 ),
    inference(superposition,[],[f78,f778])).

fof(f778,plain,
    ( k1_tsep_1(sK0,sK2,sK4) = k1_tsep_1(sK0,sK4,sK2)
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f777])).

fof(f1077,plain,
    ( spl7_110
    | spl7_106
    | spl7_5
    | spl7_9
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f382,f182,f147,f133,f119,f1042,f1075])).

fof(f1075,plain,
    ( spl7_110
  <=> k1_tsep_1(sK0,sK2,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f382,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,sK2,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK2)
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f375,f148])).

fof(f375,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,sK2,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(resolution,[],[f297,f95])).

fof(f1070,plain,
    ( spl7_108
    | spl7_3
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f945,f693,f182,f175,f147,f140,f133,f119,f112,f1068])).

fof(f1068,plain,
    ( spl7_108
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f693,plain,
    ( spl7_88
  <=> k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f945,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f944,f134])).

fof(f944,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f943,f183])).

fof(f943,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f942,f120])).

fof(f942,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f941,f176])).

fof(f941,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f940,f113])).

fof(f940,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f939,f148])).

fof(f939,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f927,f141])).

fof(f927,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_88 ),
    inference(superposition,[],[f78,f694])).

fof(f694,plain,
    ( k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2)
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f693])).

fof(f1044,plain,
    ( spl7_104
    | spl7_106
    | spl7_7
    | spl7_9
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f368,f189,f147,f133,f126,f1042,f1036])).

fof(f368,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,sK1,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK1)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f360,f148])).

fof(f360,plain,
    ( v2_struct_0(sK5(sK0))
    | k1_tsep_1(sK0,sK1,sK5(sK0)) = k1_tsep_1(sK0,sK5(sK0),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(resolution,[],[f294,f95])).

fof(f1031,plain,
    ( spl7_102
    | spl7_1
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_24
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f907,f662,f189,f154,f147,f140,f133,f126,f105,f1029])).

fof(f1029,plain,
    ( spl7_102
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f662,plain,
    ( spl7_86
  <=> k1_tsep_1(sK0,sK1,sK4) = k1_tsep_1(sK0,sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f907,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_24
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f906,f134])).

fof(f906,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_24
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f905,f190])).

fof(f905,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f904,f127])).

fof(f904,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f903,f155])).

fof(f903,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f902,f106])).

fof(f902,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f901,f148])).

fof(f901,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f889,f141])).

fof(f889,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_86 ),
    inference(superposition,[],[f78,f663])).

fof(f663,plain,
    ( k1_tsep_1(sK0,sK1,sK4) = k1_tsep_1(sK0,sK4,sK1)
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f662])).

fof(f1007,plain,
    ( spl7_98
    | spl7_100
    | spl7_5
    | spl7_7
    | ~ spl7_16
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f353,f249,f161,f126,f119,f1005,f999])).

fof(f1005,plain,
    ( spl7_100
  <=> v2_struct_0(sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f353,plain,
    ( v2_struct_0(sK5(sK2))
    | k1_tsep_1(sK2,sK1,sK5(sK2)) = k1_tsep_1(sK2,sK5(sK2),sK1)
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f348,f250])).

fof(f348,plain,
    ( v2_struct_0(sK5(sK2))
    | k1_tsep_1(sK2,sK1,sK5(sK2)) = k1_tsep_1(sK2,sK5(sK2),sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_38 ),
    inference(resolution,[],[f291,f95])).

fof(f291,plain,
    ( ! [X12] :
        ( ~ m1_pre_topc(X12,sK2)
        | v2_struct_0(X12)
        | k1_tsep_1(sK2,X12,sK1) = k1_tsep_1(sK2,sK1,X12) )
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f290,f120])).

fof(f290,plain,
    ( ! [X12] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK2)
        | v2_struct_0(sK2)
        | k1_tsep_1(sK2,X12,sK1) = k1_tsep_1(sK2,sK1,X12) )
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f289,f127])).

fof(f289,plain,
    ( ! [X12] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK2)
        | v2_struct_0(sK1)
        | v2_struct_0(sK2)
        | k1_tsep_1(sK2,X12,sK1) = k1_tsep_1(sK2,sK1,X12) )
    | ~ spl7_16
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f274,f250])).

fof(f274,plain,
    ( ! [X12] :
        ( ~ l1_pre_topc(sK2)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK2)
        | v2_struct_0(sK1)
        | v2_struct_0(sK2)
        | k1_tsep_1(sK2,X12,sK1) = k1_tsep_1(sK2,sK1,X12) )
    | ~ spl7_16 ),
    inference(resolution,[],[f77,f162])).

fof(f994,plain,
    ( spl7_96
    | spl7_3
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f886,f428,f189,f175,f147,f140,f133,f126,f112,f992])).

fof(f428,plain,
    ( spl7_46
  <=> k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f886,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f885,f134])).

fof(f885,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f884,f190])).

fof(f884,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f883,f127])).

fof(f883,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f882,f176])).

fof(f882,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f881,f113])).

fof(f881,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f880,f148])).

fof(f880,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f868,f141])).

fof(f868,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_46 ),
    inference(superposition,[],[f78,f429])).

fof(f429,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f428])).

fof(f865,plain,
    ( spl7_94
    | spl7_1
    | spl7_3
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f410,f175,f154,f147,f133,f112,f105,f863])).

fof(f410,plain,
    ( k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f404,f106])).

fof(f404,plain,
    ( v2_struct_0(sK4)
    | k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(resolution,[],[f303,f155])).

fof(f858,plain,
    ( spl7_92
    | spl7_5
    | spl7_7
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f851,f387,f189,f182,f147,f140,f133,f126,f119,f856])).

fof(f856,plain,
    ( spl7_92
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f387,plain,
    ( spl7_44
  <=> k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f851,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f850,f134])).

fof(f850,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f849,f190])).

fof(f849,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f848,f127])).

fof(f848,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f847,f183])).

fof(f847,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f846,f120])).

fof(f846,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f845,f148])).

fof(f845,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f833,f141])).

fof(f833,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_44 ),
    inference(superposition,[],[f78,f388])).

fof(f388,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f387])).

fof(f779,plain,
    ( spl7_90
    | spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f381,f182,f154,f147,f133,f119,f105,f777])).

fof(f381,plain,
    ( k1_tsep_1(sK0,sK2,sK4) = k1_tsep_1(sK0,sK4,sK2)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f374,f106])).

fof(f374,plain,
    ( v2_struct_0(sK4)
    | k1_tsep_1(sK0,sK2,sK4) = k1_tsep_1(sK0,sK4,sK2)
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(resolution,[],[f297,f155])).

fof(f710,plain,
    ( spl7_48
    | ~ spl7_51
    | ~ spl7_32
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f704,f444,f216,f441,f435])).

fof(f441,plain,
    ( spl7_51
  <=> ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f704,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_32
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f636,f445])).

fof(f636,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_32 ),
    inference(resolution,[],[f217,f86])).

fof(f703,plain,
    ( spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | spl7_55 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f701,f148])).

fof(f701,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f700,f134])).

fof(f700,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f699,f155])).

fof(f699,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_22
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f698,f106])).

fof(f698,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_5
    | ~ spl7_22
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f697,f183])).

fof(f697,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_5
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f696,f120])).

fof(f696,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_55 ),
    inference(resolution,[],[f262,f457])).

fof(f457,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl7_55
  <=> ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f262,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(k2_tsep_1(X0,X1,X2)) ) ),
    inference(resolution,[],[f81,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',dt_m1_pre_topc)).

fof(f695,plain,
    ( spl7_88
    | spl7_3
    | spl7_5
    | spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f380,f182,f175,f147,f133,f119,f112,f693])).

fof(f380,plain,
    ( k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f373,f113])).

fof(f373,plain,
    ( v2_struct_0(sK3)
    | k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2)
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(resolution,[],[f297,f176])).

fof(f664,plain,
    ( spl7_86
    | spl7_1
    | spl7_7
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f367,f189,f154,f147,f133,f126,f105,f662])).

fof(f367,plain,
    ( k1_tsep_1(sK0,sK1,sK4) = k1_tsep_1(sK0,sK4,sK1)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f359,f106])).

fof(f359,plain,
    ( v2_struct_0(sK4)
    | k1_tsep_1(sK0,sK1,sK4) = k1_tsep_1(sK0,sK4,sK1)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(resolution,[],[f294,f155])).

fof(f623,plain,
    ( ~ spl7_42
    | spl7_85 ),
    inference(avatar_contradiction_clause,[],[f622])).

fof(f622,plain,
    ( $false
    | ~ spl7_42
    | ~ spl7_85 ),
    inference(subsumption_resolution,[],[f621,f268])).

fof(f621,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl7_85 ),
    inference(resolution,[],[f616,f100])).

fof(f616,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl7_85 ),
    inference(avatar_component_clause,[],[f615])).

fof(f615,plain,
    ( spl7_85
  <=> ~ l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f620,plain,
    ( ~ spl7_38
    | spl7_83 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | ~ spl7_38
    | ~ spl7_83 ),
    inference(subsumption_resolution,[],[f618,f250])).

fof(f618,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl7_83 ),
    inference(resolution,[],[f610,f100])).

fof(f610,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl7_83
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f617,plain,
    ( spl7_80
    | ~ spl7_83
    | ~ spl7_85
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f590,f222,f615,f609,f603])).

fof(f590,plain,
    ( ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK4,sK2)
    | ~ spl7_34 ),
    inference(resolution,[],[f223,f86])).

fof(f585,plain,
    ( spl7_74
    | spl7_62
    | spl7_78
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f308,f216,f583,f481,f547])).

fof(f547,plain,
    ( spl7_74
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X0) )
    | ~ spl7_32 ),
    inference(resolution,[],[f88,f217])).

fof(f569,plain,
    ( spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_74 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f567,f134])).

fof(f567,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f566,f155])).

fof(f566,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f565,f106])).

fof(f565,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f564,f183])).

fof(f564,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f563,f120])).

fof(f563,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_12
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f562,f148])).

fof(f562,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_74 ),
    inference(resolution,[],[f548,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f548,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f547])).

fof(f561,plain,
    ( spl7_3
    | spl7_7
    | spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f559,f134])).

fof(f559,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f558,f176])).

fof(f558,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f557,f113])).

fof(f557,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f556,f190])).

fof(f556,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f555,f127])).

fof(f555,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_12
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f554,f148])).

fof(f554,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_62 ),
    inference(resolution,[],[f482,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f482,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f481])).

fof(f552,plain,
    ( spl7_62
    | spl7_74
    | spl7_76
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f307,f216,f550,f547,f481])).

fof(f307,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X0)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X1)
        | v2_struct_0(X0) )
    | ~ spl7_32 ),
    inference(resolution,[],[f87,f217])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tsep_1(X3,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f542,plain,
    ( ~ spl7_57
    | spl7_72
    | ~ spl7_61
    | spl7_62
    | spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f342,f216,f182,f154,f147,f140,f133,f119,f105,f481,f475,f540,f463])).

fof(f463,plain,
    ( spl7_57
  <=> ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f540,plain,
    ( spl7_72
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f475,plain,
    ( spl7_61
  <=> ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f342,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f341,f134])).

fof(f341,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f340,f155])).

fof(f340,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f339,f106])).

fof(f339,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f338,f183])).

fof(f338,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f337,f120])).

fof(f337,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f336,f148])).

fof(f336,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f335,f141])).

fof(f335,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_32 ),
    inference(resolution,[],[f85,f217])).

fof(f535,plain,
    ( spl7_64
    | ~ spl7_12
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f512,f472,f147,f493])).

fof(f493,plain,
    ( spl7_64
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f512,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_12
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f504,f148])).

fof(f504,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_60 ),
    inference(resolution,[],[f473,f96])).

fof(f534,plain,
    ( ~ spl7_67
    | spl7_70
    | ~ spl7_61
    | spl7_62
    | spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f334,f216,f182,f154,f147,f140,f133,f119,f105,f481,f475,f532,f519])).

fof(f519,plain,
    ( spl7_67
  <=> ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f532,plain,
    ( spl7_70
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f334,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f333,f134])).

fof(f333,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f332,f183])).

fof(f332,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f331,f120])).

fof(f331,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f330,f155])).

fof(f330,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f329,f106])).

fof(f329,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f328,f148])).

fof(f328,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f327,f141])).

fof(f327,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_32 ),
    inference(resolution,[],[f84,f217])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f527,plain,
    ( ~ spl7_67
    | spl7_68
    | ~ spl7_61
    | spl7_62
    | spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f326,f216,f182,f154,f147,f140,f133,f119,f105,f481,f475,f525,f519])).

fof(f525,plain,
    ( spl7_68
  <=> r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f326,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f325,f134])).

fof(f325,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f324,f183])).

fof(f324,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f323,f120])).

fof(f323,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f322,f155])).

fof(f322,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f321,f106])).

fof(f321,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f320,f148])).

fof(f320,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f319,f141])).

fof(f319,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK4,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK0)
    | ~ spl7_32 ),
    inference(resolution,[],[f83,f217])).

fof(f514,plain,
    ( ~ spl7_12
    | ~ spl7_60
    | spl7_65 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_60
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f512,f497])).

fof(f497,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl7_65
  <=> ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f498,plain,
    ( ~ spl7_65
    | spl7_53 ),
    inference(avatar_split_clause,[],[f451,f447,f496])).

fof(f447,plain,
    ( spl7_53
  <=> ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f451,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_53 ),
    inference(resolution,[],[f448,f100])).

fof(f448,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f447])).

fof(f491,plain,
    ( spl7_3
    | spl7_7
    | spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | spl7_61 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f489,f134])).

fof(f489,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f488,f176])).

fof(f488,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f487,f113])).

fof(f487,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f486,f190])).

fof(f486,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f485,f127])).

fof(f485,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_12
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f484,f148])).

fof(f484,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_61 ),
    inference(resolution,[],[f476,f76])).

fof(f476,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f475])).

fof(f483,plain,
    ( ~ spl7_57
    | spl7_58
    | ~ spl7_61
    | spl7_62
    | spl7_1
    | spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f318,f216,f182,f154,f147,f140,f133,f119,f105,f481,f475,f469,f463])).

fof(f469,plain,
    ( spl7_58
  <=> r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f318,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f317,f134])).

fof(f317,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f316,f155])).

fof(f316,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f315,f106])).

fof(f315,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f314,f183])).

fof(f314,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f313,f120])).

fof(f313,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f312,f148])).

fof(f312,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f311,f141])).

fof(f311,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | r1_tsep_1(sK2,k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK4)
    | v2_struct_0(sK0)
    | ~ spl7_32 ),
    inference(resolution,[],[f82,f217])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f458,plain,
    ( ~ spl7_55
    | spl7_51 ),
    inference(avatar_split_clause,[],[f450,f441,f456])).

fof(f450,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_51 ),
    inference(resolution,[],[f442,f100])).

fof(f442,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f441])).

fof(f449,plain,
    ( spl7_48
    | ~ spl7_51
    | ~ spl7_53
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f244,f216,f447,f441,f435])).

fof(f244,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_32 ),
    inference(resolution,[],[f86,f217])).

fof(f430,plain,
    ( spl7_46
    | spl7_3
    | spl7_7
    | spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f366,f189,f175,f147,f133,f126,f112,f428])).

fof(f366,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f358,f113])).

fof(f358,plain,
    ( v2_struct_0(sK3)
    | k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24 ),
    inference(resolution,[],[f294,f176])).

fof(f389,plain,
    ( spl7_44
    | spl7_5
    | spl7_7
    | spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f365,f189,f182,f147,f133,f126,f119,f387])).

fof(f365,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f357,f120])).

fof(f357,plain,
    ( v2_struct_0(sK2)
    | k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(resolution,[],[f294,f183])).

fof(f344,plain,
    ( spl7_40
    | ~ spl7_43
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f228,f168,f264,f256])).

fof(f264,plain,
    ( spl7_43
  <=> ~ l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f228,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f96,f169])).

fof(f343,plain,
    ( spl7_36
    | ~ spl7_39
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f225,f161,f246,f241])).

fof(f241,plain,
    ( spl7_36
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f246,plain,
    ( spl7_39
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f96,f162])).

fof(f269,plain,
    ( spl7_42
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f236,f154,f147,f267])).

fof(f236,plain,
    ( l1_pre_topc(sK4)
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f230,f148])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK4)
    | ~ spl7_14 ),
    inference(resolution,[],[f96,f155])).

fof(f258,plain,
    ( spl7_40
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f235,f175,f147,f256])).

fof(f235,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f229,f148])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl7_20 ),
    inference(resolution,[],[f96,f176])).

fof(f251,plain,
    ( spl7_38
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f234,f182,f147,f249])).

fof(f234,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f227,f148])).

fof(f227,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl7_22 ),
    inference(resolution,[],[f96,f183])).

fof(f243,plain,
    ( spl7_36
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f233,f189,f147,f241])).

fof(f233,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f226,f148])).

fof(f226,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl7_24 ),
    inference(resolution,[],[f96,f190])).

fof(f224,plain,
    ( spl7_32
    | spl7_34 ),
    inference(avatar_split_clause,[],[f60,f222,f216])).

fof(f60,plain,
    ( r1_tsep_1(sK2,sK4)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => ( ( r1_tsep_1(X4,X1)
                              & r1_tsep_1(X2,X3) )
                            | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                              & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => ( ( r1_tsep_1(X4,X1)
                            & r1_tsep_1(X2,X3) )
                          | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                            & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t35_tmap_1)).

fof(f211,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f97,f209])).

fof(f209,plain,
    ( spl7_30
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f97,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',existence_l1_pre_topc)).

fof(f204,plain,
    ( ~ spl7_27
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f59,f202,f196])).

fof(f59,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f191,plain,(
    spl7_24 ),
    inference(avatar_split_clause,[],[f70,f189])).

fof(f70,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f184,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f68,f182])).

fof(f68,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f177,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f66,f175])).

fof(f66,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f170,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f64,f168])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f163,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f63,f161])).

fof(f63,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f156,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f62,f154])).

fof(f62,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f149,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f73,f147])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f142,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f72,f140])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f135,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f71,f133])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f128,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f69,f126])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f121,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f67,f119])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f65,f112])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f61,f105])).

fof(f61,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
