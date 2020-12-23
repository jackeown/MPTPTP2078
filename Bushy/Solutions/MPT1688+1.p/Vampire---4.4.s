%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t68_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 352 expanded)
%              Number of leaves         :   24 ( 134 expanded)
%              Depth                    :   24
%              Number of atoms          :  988 (2122 expanded)
%              Number of equality atoms :   31 ( 106 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f106,f110,f114,f118,f122,f128,f132,f136,f146,f150,f158,f166,f257,f261,f279,f283,f287,f314,f418])).

fof(f418,plain,
    ( ~ spl9_0
    | ~ spl9_2
    | spl9_5
    | ~ spl9_6
    | spl9_9
    | ~ spl9_10
    | spl9_15
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_15
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f416,f131])).

fof(f131,plain,
    ( ~ v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl9_15
  <=> ~ v23_waybel_0(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f416,plain,
    ( v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f415,f113])).

fof(f113,plain,
    ( l1_orders_2(sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl9_6
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f415,plain,
    ( ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_36
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f414,f278])).

fof(f278,plain,
    ( v5_orders_3(sK3,sK1,sK0)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl9_36
  <=> v5_orders_3(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f414,plain,
    ( ~ v5_orders_3(sK3,sK1,sK0)
    | ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f413,f117])).

fof(f117,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_9
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f413,plain,
    ( v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f412,f109])).

fof(f109,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl9_5
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f412,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f411,f286])).

fof(f286,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl9_40
  <=> v5_orders_3(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f411,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f410,f145])).

fof(f145,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl9_18
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f410,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f409,f121])).

fof(f121,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_10
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f409,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f408,f165])).

fof(f165,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl9_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f408,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f407,f149])).

fof(f149,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_20
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f407,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v5_orders_3(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v5_orders_3(sK3,sK1,sK0)
    | ~ l1_orders_2(sK1)
    | v23_waybel_0(sK3,sK1,sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_24
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(resolution,[],[f322,f157])).

fof(f157,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl9_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v5_orders_3(sK2,X0,X1)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ l1_orders_2(X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f321,f313])).

fof(f313,plain,
    ( k2_funct_1(sK3) = sK2
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl9_48
  <=> k2_funct_1(sK3) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f321,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(k2_funct_1(sK3),X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f320,f313])).

fof(f320,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(k2_funct_1(sK3),X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f319,f105])).

fof(f105,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl9_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f319,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(k2_funct_1(sK3),X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl9_0
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f318,f313])).

fof(f318,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(k2_funct_1(sK3),X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl9_0
    | ~ spl9_38
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f317,f282])).

fof(f282,plain,
    ( v2_funct_1(sK3)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl9_38
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f317,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_funct_1(sK3)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(k2_funct_1(sK3),X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl9_0
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f316,f101])).

fof(f101,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f316,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ l1_orders_2(X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_funct_1(sK3)
        | ~ v5_orders_3(sK3,X1,X0)
        | ~ v1_funct_1(k2_funct_1(sK3))
        | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v5_orders_3(k2_funct_1(sK3),X0,X1)
        | v23_waybel_0(sK3,X1,X0) )
    | ~ spl9_48 ),
    inference(superposition,[],[f98,f313])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_3(k2_funct_1(X2),X1,X0)
      | v23_waybel_0(X2,X0,X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | k2_funct_1(X2) != X3
      | ~ v5_orders_3(X3,X1,X0)
      | v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( ~ ( ~ v2_struct_0(X1)
                      & ~ v2_struct_0(X0) )
                 => ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) ) )
                & ~ ( ~ ( v23_waybel_0(X2,X0,X1)
                      <=> ( ? [X3] :
                              ( v5_orders_3(X3,X1,X0)
                              & k2_funct_1(X2) = X3
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                              & v1_funct_1(X3) )
                          & v5_orders_3(X2,X0,X1)
                          & v2_funct_1(X2) ) )
                    & ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',d38_waybel_0)).

fof(f314,plain,
    ( spl9_48
    | ~ spl9_2
    | ~ spl9_12
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f275,f259,f255,f126,f104,f312])).

fof(f126,plain,
    ( spl9_12
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f255,plain,
    ( spl9_32
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f259,plain,
    ( spl9_34
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f275,plain,
    ( k2_funct_1(sK3) = sK2
    | ~ spl9_2
    | ~ spl9_12
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f274,f127])).

fof(f127,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f274,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | ~ spl9_2
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f273,f256])).

fof(f256,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f255])).

fof(f273,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | ~ spl9_2
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f269,f105])).

fof(f269,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | ~ spl9_34 ),
    inference(resolution,[],[f260,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',t65_funct_1)).

fof(f260,plain,
    ( v2_funct_1(sK2)
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f259])).

fof(f287,plain,
    ( spl9_40
    | ~ spl9_2
    | spl9_5
    | ~ spl9_6
    | spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f249,f164,f148,f134,f120,f116,f112,f108,f104,f285])).

fof(f134,plain,
    ( spl9_16
  <=> v23_waybel_0(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f249,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f248,f135])).

fof(f135,plain,
    ( v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f248,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f247,f109])).

fof(f247,plain,
    ( v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f246,f117])).

fof(f246,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f245,f121])).

fof(f245,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f244,f149])).

fof(f244,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f243,f105])).

fof(f243,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f191,f113])).

fof(f191,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_28 ),
    inference(resolution,[],[f165,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v5_orders_3(X2,X0,X1)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f283,plain,
    ( spl9_38
    | ~ spl9_2
    | ~ spl9_12
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f272,f259,f255,f126,f104,f281])).

fof(f272,plain,
    ( v2_funct_1(sK3)
    | ~ spl9_2
    | ~ spl9_12
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f271,f127])).

fof(f271,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl9_2
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f270,f256])).

fof(f270,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl9_2
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f268,f105])).

fof(f268,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl9_34 ),
    inference(resolution,[],[f260,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',t62_funct_1)).

fof(f279,plain,
    ( spl9_36
    | ~ spl9_2
    | spl9_5
    | ~ spl9_6
    | spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f234,f164,f148,f134,f126,f120,f116,f112,f108,f104,f277])).

fof(f234,plain,
    ( v5_orders_3(sK3,sK1,sK0)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f233,f226])).

fof(f226,plain,
    ( sK3 = sK5(sK0,sK1,sK2)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f225,f127])).

fof(f225,plain,
    ( k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f224,f135])).

fof(f224,plain,
    ( k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f223,f109])).

fof(f223,plain,
    ( v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f222,f117])).

fof(f222,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f221,f121])).

fof(f221,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f220,f149])).

fof(f220,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f219,f105])).

fof(f219,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f188,f113])).

fof(f188,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_28 ),
    inference(resolution,[],[f165,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | k2_funct_1(X2) = sK5(X0,X1,X2)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f233,plain,
    ( v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f232,f135])).

fof(f232,plain,
    ( v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f231,f109])).

fof(f231,plain,
    ( v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f230,f117])).

fof(f230,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f229,f121])).

fof(f229,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f228,f149])).

fof(f228,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f227,f105])).

fof(f227,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f189,f113])).

fof(f189,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_28 ),
    inference(resolution,[],[f165,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v5_orders_3(sK5(X0,X1,X2),X1,X0)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f261,plain,
    ( spl9_34
    | ~ spl9_2
    | spl9_5
    | ~ spl9_6
    | spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f241,f164,f148,f134,f120,f116,f112,f108,f104,f259])).

fof(f241,plain,
    ( v2_funct_1(sK2)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f240,f135])).

fof(f240,plain,
    ( v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f239,f109])).

fof(f239,plain,
    ( v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f238,f117])).

fof(f238,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f237,f121])).

fof(f237,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_20
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f236,f149])).

fof(f236,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f235,f105])).

fof(f235,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f190,f113])).

fof(f190,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl9_28 ),
    inference(resolution,[],[f165,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v2_funct_1(X2)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f257,plain,
    ( spl9_32
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f196,f164,f255])).

fof(f196,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_28 ),
    inference(resolution,[],[f165,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',cc1_relset_1)).

fof(f166,plain,(
    spl9_28 ),
    inference(avatar_split_clause,[],[f62,f164])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X3) )
                     => ( k2_funct_1(X2) = X3
                       => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( k2_funct_1(X2) = X3
                     => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',t68_waybel_0)).

fof(f158,plain,(
    spl9_24 ),
    inference(avatar_split_clause,[],[f57,f156])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f150,plain,(
    spl9_20 ),
    inference(avatar_split_clause,[],[f61,f148])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f146,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f56,f144])).

fof(f56,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f136,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f63,f134])).

fof(f63,plain,(
    v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f132,plain,(
    ~ spl9_15 ),
    inference(avatar_split_clause,[],[f59,f130])).

fof(f59,plain,(
    ~ v23_waybel_0(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f128,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f58,f126])).

fof(f58,plain,(
    k2_funct_1(sK2) = sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f122,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f67,f120])).

fof(f67,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f66,f116])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f114,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f65,f112])).

fof(f65,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f110,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f64,f108])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f60,f104])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f55,f100])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
