%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 760 expanded)
%              Number of leaves         :   49 ( 392 expanded)
%              Depth                    :   25
%              Number of atoms          : 1190 (6913 expanded)
%              Number of equality atoms :  126 (1319 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f88,f93,f98,f103,f109,f114,f119,f124,f129,f134,f139,f156,f169,f174,f181,f192,f197,f240,f245,f254,f268,f314,f337,f444,f449,f482,f512,f517,f537,f547,f587])).

fof(f587,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_26
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33
    | ~ spl10_36
    | ~ spl10_38
    | spl10_40
    | ~ spl10_41 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_26
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33
    | ~ spl10_36
    | ~ spl10_38
    | spl10_40
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f585,f536])).

fof(f536,plain,
    ( ~ r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))
    | spl10_40 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl10_40
  <=> r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f585,plain,
    ( r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_26
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_41 ),
    inference(forward_demodulation,[],[f584,f253])).

fof(f253,plain,
    ( sK8(sK2,sK3,sK4) = k1_funct_1(sK4,sK6(sK2,sK3,sK4))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl10_26
  <=> sK8(sK2,sK3,sK4) = k1_funct_1(sK4,sK6(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f584,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK4,sK6(sK2,sK3,sK4)),sK9(sK2,sK3,sK4))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_26
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f583,f516])).

fof(f516,plain,
    ( m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f514])).

fof(f514,plain,
    ( spl10_38
  <=> m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f583,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1))
    | r1_orders_2(sK1,k1_funct_1(sK4,sK6(sK2,sK3,sK4)),sK9(sK2,sK3,sK4))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_26
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33
    | ~ spl10_36
    | ~ spl10_41 ),
    inference(forward_demodulation,[],[f582,f253])).

fof(f582,plain,
    ( ~ m1_subset_1(k1_funct_1(sK4,sK6(sK2,sK3,sK4)),u1_struct_0(sK1))
    | r1_orders_2(sK1,k1_funct_1(sK4,sK6(sK2,sK3,sK4)),sK9(sK2,sK3,sK4))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33
    | ~ spl10_36
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f581,f481])).

fof(f481,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK0))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl10_36
  <=> m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f581,plain,
    ( ~ m1_subset_1(k1_funct_1(sK4,sK6(sK2,sK3,sK4)),u1_struct_0(sK1))
    | r1_orders_2(sK1,k1_funct_1(sK4,sK6(sK2,sK3,sK4)),sK9(sK2,sK3,sK4))
    | ~ m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33
    | ~ spl10_41 ),
    inference(resolution,[],[f546,f507])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f506,f67])).

fof(f67,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl10_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f506,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f505,f72])).

fof(f72,plain,
    ( l1_orders_2(sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl10_2
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f505,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f504,f113])).

fof(f113,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_10
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f504,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f503,f123])).

fof(f123,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl10_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f503,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_29
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f502,f403])).

fof(f403,plain,
    ( m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK1))
    | ~ spl10_19
    | ~ spl10_33 ),
    inference(superposition,[],[f180,f336])).

fof(f336,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK3)
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl10_33
  <=> u1_struct_0(sK1) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f180,plain,
    ( m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK3))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl10_19
  <=> m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f502,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_17
    | ~ spl10_29
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f501,f352])).

fof(f352,plain,
    ( m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK0))
    | ~ spl10_17
    | ~ spl10_30 ),
    inference(superposition,[],[f168,f313])).

fof(f313,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK2)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl10_30
  <=> u1_struct_0(sK0) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f168,plain,
    ( m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl10_17
  <=> m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f501,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_29 ),
    inference(resolution,[],[f272,f97])).

fof(f97,plain,
    ( v5_orders_3(sK4,sK0,sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl10_7
  <=> v5_orders_3(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f272,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_3(sK4,X2,X0)
        | r1_orders_2(X0,k1_funct_1(sK4,X1),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X1),u1_struct_0(X0))
        | ~ r1_orders_2(X2,X1,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(X2) )
    | ~ spl10_5
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f271,f87])).

fof(f87,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_5
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f271,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(X0))
        | r1_orders_2(X0,k1_funct_1(sK4,X1),sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(k1_funct_1(sK4,X1),u1_struct_0(X0))
        | ~ r1_orders_2(X2,X1,sK7(sK2,sK3,sK4))
        | ~ m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ v5_orders_3(sK4,X2,X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X0))
        | ~ v1_funct_1(sK4)
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(X2) )
    | ~ spl10_29 ),
    inference(superposition,[],[f60,f267])).

fof(f267,plain,
    ( sK9(sK2,sK3,sK4) = k1_funct_1(sK4,sK7(sK2,sK3,sK4))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl10_29
  <=> sK9(sK2,sK3,sK4) = k1_funct_1(sK4,sK7(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f60,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ m1_subset_1(k1_funct_1(X2,X8),u1_struct_0(X1))
      | r1_orders_2(X1,k1_funct_1(X2,X7),k1_funct_1(X2,X8))
      | ~ m1_subset_1(k1_funct_1(X2,X7),u1_struct_0(X1))
      | ~ r1_orders_2(X0,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r1_orders_2(X1,X9,k1_funct_1(X2,X8))
      | k1_funct_1(X2,X7) != X9
      | ~ m1_subset_1(k1_funct_1(X2,X8),u1_struct_0(X1))
      | ~ m1_subset_1(X9,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X10,X8,X7,X1,X9] :
      ( r1_orders_2(X1,X9,X10)
      | k1_funct_1(X2,X8) != X10
      | k1_funct_1(X2,X7) != X9
      | ~ m1_subset_1(X10,u1_struct_0(X1))
      | ~ m1_subset_1(X9,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_orders_3(X2,X0,X1)
                  | ( ~ r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2))
                    & k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2)
                    & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
                    & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
                    & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
                    & r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
                    & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
                    & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( ! [X10] :
                                  ( r1_orders_2(X1,X9,X10)
                                  | k1_funct_1(X2,X8) != X10
                                  | k1_funct_1(X2,X7) != X9
                                  | ~ m1_subset_1(X10,u1_struct_0(X1)) )
                              | ~ m1_subset_1(X9,u1_struct_0(X1)) )
                          | ~ r1_orders_2(X0,X7,X8)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ v5_orders_3(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f23,f27,f26,f25,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(X1,X5,X6)
                      & k1_funct_1(X2,X4) = X6
                      & k1_funct_1(X2,X3) = X5
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & r1_orders_2(X0,X3,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(X1,X5,X6)
                    & k1_funct_1(X2,X4) = X6
                    & k1_funct_1(X2,sK6(X0,X1,X2)) = X5
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & r1_orders_2(X0,sK6(X0,X1,X2),X4)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(X1,X5,X6)
                  & k1_funct_1(X2,X4) = X6
                  & k1_funct_1(X2,sK6(X0,X1,X2)) = X5
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_orders_2(X0,sK6(X0,X1,X2),X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(X1,X5,X6)
                & k1_funct_1(X2,sK7(X0,X1,X2)) = X6
                & k1_funct_1(X2,sK6(X0,X1,X2)) = X5
                & m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(X1,X5,X6)
              & k1_funct_1(X2,sK7(X0,X1,X2)) = X6
              & k1_funct_1(X2,sK6(X0,X1,X2)) = X5
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
            & k1_funct_1(X2,sK7(X0,X1,X2)) = X6
            & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
          & k1_funct_1(X2,sK7(X0,X1,X2)) = X6
          & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2))
        & k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2)
        & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_orders_3(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ? [X6] :
                                  ( ~ r1_orders_2(X1,X5,X6)
                                  & k1_funct_1(X2,X4) = X6
                                  & k1_funct_1(X2,X3) = X5
                                  & m1_subset_1(X6,u1_struct_0(X1)) )
                              & m1_subset_1(X5,u1_struct_0(X1)) )
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( ! [X10] :
                                  ( r1_orders_2(X1,X9,X10)
                                  | k1_funct_1(X2,X8) != X10
                                  | k1_funct_1(X2,X7) != X9
                                  | ~ m1_subset_1(X10,u1_struct_0(X1)) )
                              | ~ m1_subset_1(X9,u1_struct_0(X1)) )
                          | ~ r1_orders_2(X0,X7,X8)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ v5_orders_3(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_orders_3(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ? [X6] :
                                  ( ~ r1_orders_2(X1,X5,X6)
                                  & k1_funct_1(X2,X4) = X6
                                  & k1_funct_1(X2,X3) = X5
                                  & m1_subset_1(X6,u1_struct_0(X1)) )
                              & m1_subset_1(X5,u1_struct_0(X1)) )
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ! [X6] :
                                  ( r1_orders_2(X1,X5,X6)
                                  | k1_funct_1(X2,X4) != X6
                                  | k1_funct_1(X2,X3) != X5
                                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                          | ~ r1_orders_2(X0,X3,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ v5_orders_3(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_orders_2(X0,X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X1))
                                 => ( ( k1_funct_1(X2,X4) = X6
                                      & k1_funct_1(X2,X3) = X5 )
                                   => r1_orders_2(X1,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_3)).

fof(f546,plain,
    ( r1_orders_2(sK0,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl10_41
  <=> r1_orders_2(sK0,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f547,plain,
    ( spl10_41
    | ~ spl10_1
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f525,f509,f479,f441,f65,f544])).

fof(f441,plain,
    ( spl10_34
  <=> r2_hidden(k4_tarski(sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f509,plain,
    ( spl10_37
  <=> m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f525,plain,
    ( r1_orders_2(sK0,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4))
    | ~ spl10_1
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f67,f481,f443,f511,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

% (30315)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f511,plain,
    ( m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK0))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f509])).

fof(f443,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)),u1_orders_2(sK0))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f441])).

fof(f537,plain,
    ( ~ spl10_40
    | ~ spl10_2
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_33
    | spl10_35 ),
    inference(avatar_split_clause,[],[f453,f446,f334,f178,f171,f70,f534])).

fof(f171,plain,
    ( spl10_18
  <=> m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f446,plain,
    ( spl10_35
  <=> r2_hidden(k4_tarski(sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f453,plain,
    ( ~ r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))
    | ~ spl10_2
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_33
    | spl10_35 ),
    inference(subsumption_resolution,[],[f452,f72])).

fof(f452,plain,
    ( ~ r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK1)
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_33
    | spl10_35 ),
    inference(subsumption_resolution,[],[f451,f402])).

fof(f402,plain,
    ( m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1))
    | ~ spl10_18
    | ~ spl10_33 ),
    inference(superposition,[],[f173,f336])).

fof(f173,plain,
    ( m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK3))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f451,plain,
    ( ~ r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl10_19
    | ~ spl10_33
    | spl10_35 ),
    inference(subsumption_resolution,[],[f450,f403])).

fof(f450,plain,
    ( ~ r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))
    | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl10_35 ),
    inference(resolution,[],[f448,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f448,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)),u1_orders_2(sK1))
    | spl10_35 ),
    inference(avatar_component_clause,[],[f446])).

fof(f517,plain,
    ( spl10_38
    | ~ spl10_18
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f402,f334,f171,f514])).

fof(f512,plain,
    ( spl10_37
    | ~ spl10_17
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f352,f311,f166,f509])).

fof(f482,plain,
    ( spl10_36
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f351,f311,f153,f479])).

fof(f153,plain,
    ( spl10_16
  <=> m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f351,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK0))
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(superposition,[],[f155,f313])).

fof(f155,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f449,plain,
    ( ~ spl10_35
    | ~ spl10_4
    | ~ spl10_15
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_21
    | spl10_25 ),
    inference(avatar_split_clause,[],[f249,f242,f194,f178,f171,f136,f80,f446])).

fof(f80,plain,
    ( spl10_4
  <=> l1_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f136,plain,
    ( spl10_15
  <=> g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f194,plain,
    ( spl10_21
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f242,plain,
    ( spl10_25
  <=> r1_orders_2(sK3,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f249,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)),u1_orders_2(sK1))
    | ~ spl10_4
    | ~ spl10_15
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_21
    | spl10_25 ),
    inference(forward_demodulation,[],[f248,f212])).

fof(f212,plain,
    ( u1_orders_2(sK1) = u1_orders_2(sK3)
    | ~ spl10_15
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f138,f196,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f196,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f194])).

fof(f138,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f248,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)),u1_orders_2(sK3))
    | ~ spl10_4
    | ~ spl10_18
    | ~ spl10_19
    | spl10_25 ),
    inference(unit_resulting_resolution,[],[f82,f173,f180,f244,f56])).

fof(f244,plain,
    ( ~ r1_orders_2(sK3,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))
    | spl10_25 ),
    inference(avatar_component_clause,[],[f242])).

fof(f82,plain,
    ( l1_orders_2(sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f444,plain,
    ( spl10_34
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f247,f237,f189,f166,f153,f131,f75,f441])).

fof(f75,plain,
    ( spl10_3
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f131,plain,
    ( spl10_14
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f189,plain,
    ( spl10_20
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f237,plain,
    ( spl10_24
  <=> r1_orders_2(sK2,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f247,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)),u1_orders_2(sK0))
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f246,f208])).

fof(f208,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK2)
    | ~ spl10_14
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f133,f191,f58])).

fof(f191,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f133,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f246,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)),u1_orders_2(sK2))
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f77,f155,f168,f239,f55])).

fof(f239,plain,
    ( r1_orders_2(sK2,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f237])).

fof(f77,plain,
    ( l1_orders_2(sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f337,plain,
    ( spl10_33
    | ~ spl10_15
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f213,f194,f136,f334])).

fof(f213,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK3)
    | ~ spl10_15
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f138,f196,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f314,plain,
    ( spl10_30
    | ~ spl10_14
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f209,f189,f131,f311])).

fof(f209,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK2)
    | ~ spl10_14
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f133,f191,f57])).

fof(f268,plain,
    ( spl10_29
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f163,f126,f116,f106,f85,f80,f75,f265])).

fof(f106,plain,
    ( spl10_9
  <=> v5_orders_3(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f116,plain,
    ( spl10_11
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f126,plain,
    ( spl10_13
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f163,plain,
    ( sK9(sK2,sK3,sK4) = k1_funct_1(sK4,sK7(sK2,sK3,sK4))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_orders_3(X2,X0,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f128,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f118,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f108,plain,
    ( ~ v5_orders_3(sK4,sK2,sK3)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f254,plain,
    ( spl10_26
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f161,f126,f116,f106,f85,f80,f75,f251])).

fof(f161,plain,
    ( sK8(sK2,sK3,sK4) = k1_funct_1(sK4,sK6(sK2,sK3,sK4))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_orders_3(X2,X0,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f245,plain,
    ( ~ spl10_25
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f160,f126,f116,f106,f85,f80,f75,f242])).

fof(f160,plain,
    ( ~ r1_orders_2(sK3,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2))
      | v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f240,plain,
    ( spl10_24
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f159,f126,f116,f106,f85,f80,f75,f237])).

fof(f159,plain,
    ( r1_orders_2(sK2,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
      | v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f197,plain,
    ( spl10_21
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f141,f70,f194])).

fof(f141,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f192,plain,
    ( spl10_20
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f140,f65,f189])).

fof(f140,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f67,f45])).

fof(f181,plain,
    ( spl10_19
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f157,f126,f116,f106,f85,f80,f75,f178])).

fof(f157,plain,
    ( m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK3))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_orders_3(X2,X0,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f174,plain,
    ( spl10_18
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f150,f126,f116,f106,f85,f80,f75,f171])).

fof(f150,plain,
    ( m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK3))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_orders_3(X2,X0,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f169,plain,
    ( spl10_17
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f148,f126,f116,f106,f85,f80,f75,f166])).

fof(f148,plain,
    ( m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_orders_3(X2,X0,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f156,plain,
    ( spl10_16
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f146,f126,f116,f106,f85,f80,f75,f153])).

fof(f146,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_9
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_orders_3(X2,X0,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f139,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f41,f136])).

fof(f41,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v5_orders_3(sK5,sK2,sK3)
    & v5_orders_3(sK4,sK0,sK1)
    & sK4 = sK5
    & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & l1_orders_2(sK3)
    & l1_orders_2(sK2)
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f20,f19,f18,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ v5_orders_3(X5,X2,X3)
                            & v5_orders_3(X4,X0,X1)
                            & X4 = X5
                            & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & l1_orders_2(X3) )
                & l1_orders_2(X2) )
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,sK0,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ v5_orders_3(X5,X2,X3)
                        & v5_orders_3(X4,sK0,X1)
                        & X4 = X5
                        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                        & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & l1_orders_2(X3) )
            & l1_orders_2(X2) )
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ v5_orders_3(X5,X2,X3)
                      & v5_orders_3(X4,sK0,sK1)
                      & X4 = X5
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
                      & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & l1_orders_2(X3) )
          & l1_orders_2(X2) )
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ v5_orders_3(X5,X2,X3)
                    & v5_orders_3(X4,sK0,sK1)
                    & X4 = X5
                    & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
                    & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & l1_orders_2(X3) )
        & l1_orders_2(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ v5_orders_3(X5,sK2,X3)
                  & v5_orders_3(X4,sK0,sK1)
                  & X4 = X5
                  & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
                  & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                  & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & l1_orders_2(X3) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ v5_orders_3(X5,sK2,X3)
                & v5_orders_3(X4,sK0,sK1)
                & X4 = X5
                & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
                & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & l1_orders_2(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ v5_orders_3(X5,sK2,sK3)
              & v5_orders_3(X4,sK0,sK1)
              & X4 = X5
              & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
              & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ v5_orders_3(X5,sK2,sK3)
            & v5_orders_3(X4,sK0,sK1)
            & X4 = X5
            & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
            & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ v5_orders_3(X5,sK2,sK3)
          & v5_orders_3(sK4,sK0,sK1)
          & sK4 = X5
          & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X5] :
        ( ~ v5_orders_3(X5,sK2,sK3)
        & v5_orders_3(sK4,sK0,sK1)
        & sK4 = X5
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X5) )
   => ( ~ v5_orders_3(sK5,sK2,sK3)
      & v5_orders_3(sK4,sK0,sK1)
      & sK4 = sK5
      & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,X0,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,X0,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ! [X2] :
                ( l1_orders_2(X2)
               => ! [X3] :
                    ( l1_orders_2(X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                           => ( ( v5_orders_3(X4,X0,X1)
                                & X4 = X5
                                & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                             => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ! [X2] :
                ( ( l1_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( l1_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                           => ( ( v5_orders_3(X4,X0,X1)
                                & X4 = X5
                                & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                             => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( l1_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( l1_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                         => ( ( v5_orders_3(X4,X0,X1)
                              & X4 = X5
                              & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                           => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_waybel_9)).

fof(f134,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f40,f131])).

fof(f40,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f129,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f61,f126])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f39,f42])).

fof(f42,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f124,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f36,f121])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f119,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f62,f116])).

fof(f62,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f38,f42])).

fof(f38,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f114,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f35,f111])).

fof(f35,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,
    ( ~ spl10_9
    | ~ spl10_6
    | spl10_8 ),
    inference(avatar_split_clause,[],[f104,f100,f90,f106])).

fof(f90,plain,
    ( spl10_6
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f100,plain,
    ( spl10_8
  <=> v5_orders_3(sK5,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f104,plain,
    ( ~ v5_orders_3(sK4,sK2,sK3)
    | ~ spl10_6
    | spl10_8 ),
    inference(forward_demodulation,[],[f102,f92])).

fof(f92,plain,
    ( sK4 = sK5
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f102,plain,
    ( ~ v5_orders_3(sK5,sK2,sK3)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,(
    ~ spl10_8 ),
    inference(avatar_split_clause,[],[f44,f100])).

fof(f44,plain,(
    ~ v5_orders_3(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f43,f95])).

fof(f43,plain,(
    v5_orders_3(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f42,f90])).

fof(f88,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f63,f85])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(forward_demodulation,[],[f37,f42])).

fof(f37,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (30313)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (30321)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (30305)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (30298)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (30303)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (30298)Refutation not found, incomplete strategy% (30298)------------------------------
% 0.21/0.51  % (30298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30298)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30298)Memory used [KB]: 10618
% 0.21/0.51  % (30298)Time elapsed: 0.093 s
% 0.21/0.51  % (30298)------------------------------
% 0.21/0.51  % (30298)------------------------------
% 0.21/0.51  % (30302)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (30305)Refutation not found, incomplete strategy% (30305)------------------------------
% 0.21/0.51  % (30305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30305)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30305)Memory used [KB]: 1791
% 0.21/0.51  % (30305)Time elapsed: 0.037 s
% 0.21/0.51  % (30305)------------------------------
% 0.21/0.51  % (30305)------------------------------
% 0.21/0.51  % (30322)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (30308)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (30321)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f588,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f88,f93,f98,f103,f109,f114,f119,f124,f129,f134,f139,f156,f169,f174,f181,f192,f197,f240,f245,f254,f268,f314,f337,f444,f449,f482,f512,f517,f537,f547,f587])).
% 0.21/0.52  fof(f587,plain,(
% 0.21/0.52    ~spl10_1 | ~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_26 | ~spl10_29 | ~spl10_30 | ~spl10_33 | ~spl10_36 | ~spl10_38 | spl10_40 | ~spl10_41),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f586])).
% 0.21/0.52  fof(f586,plain,(
% 0.21/0.52    $false | (~spl10_1 | ~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_26 | ~spl10_29 | ~spl10_30 | ~spl10_33 | ~spl10_36 | ~spl10_38 | spl10_40 | ~spl10_41)),
% 0.21/0.52    inference(subsumption_resolution,[],[f585,f536])).
% 0.21/0.52  fof(f536,plain,(
% 0.21/0.52    ~r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) | spl10_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f534])).
% 0.21/0.52  fof(f534,plain,(
% 0.21/0.52    spl10_40 <=> r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.21/0.52  fof(f585,plain,(
% 0.21/0.52    r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) | (~spl10_1 | ~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_26 | ~spl10_29 | ~spl10_30 | ~spl10_33 | ~spl10_36 | ~spl10_38 | ~spl10_41)),
% 0.21/0.52    inference(forward_demodulation,[],[f584,f253])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    sK8(sK2,sK3,sK4) = k1_funct_1(sK4,sK6(sK2,sK3,sK4)) | ~spl10_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f251])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    spl10_26 <=> sK8(sK2,sK3,sK4) = k1_funct_1(sK4,sK6(sK2,sK3,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.21/0.52  fof(f584,plain,(
% 0.21/0.52    r1_orders_2(sK1,k1_funct_1(sK4,sK6(sK2,sK3,sK4)),sK9(sK2,sK3,sK4)) | (~spl10_1 | ~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_26 | ~spl10_29 | ~spl10_30 | ~spl10_33 | ~spl10_36 | ~spl10_38 | ~spl10_41)),
% 0.21/0.52    inference(subsumption_resolution,[],[f583,f516])).
% 0.21/0.52  fof(f516,plain,(
% 0.21/0.52    m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1)) | ~spl10_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f514])).
% 0.21/0.52  fof(f514,plain,(
% 0.21/0.52    spl10_38 <=> m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.21/0.52  fof(f583,plain,(
% 0.21/0.52    ~m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1)) | r1_orders_2(sK1,k1_funct_1(sK4,sK6(sK2,sK3,sK4)),sK9(sK2,sK3,sK4)) | (~spl10_1 | ~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_26 | ~spl10_29 | ~spl10_30 | ~spl10_33 | ~spl10_36 | ~spl10_41)),
% 0.21/0.52    inference(forward_demodulation,[],[f582,f253])).
% 0.21/0.52  fof(f582,plain,(
% 0.21/0.52    ~m1_subset_1(k1_funct_1(sK4,sK6(sK2,sK3,sK4)),u1_struct_0(sK1)) | r1_orders_2(sK1,k1_funct_1(sK4,sK6(sK2,sK3,sK4)),sK9(sK2,sK3,sK4)) | (~spl10_1 | ~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_29 | ~spl10_30 | ~spl10_33 | ~spl10_36 | ~spl10_41)),
% 0.21/0.52    inference(subsumption_resolution,[],[f581,f481])).
% 0.21/0.52  fof(f481,plain,(
% 0.21/0.52    m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK0)) | ~spl10_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f479])).
% 0.21/0.52  fof(f479,plain,(
% 0.21/0.52    spl10_36 <=> m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.21/0.52  fof(f581,plain,(
% 0.21/0.52    ~m1_subset_1(k1_funct_1(sK4,sK6(sK2,sK3,sK4)),u1_struct_0(sK1)) | r1_orders_2(sK1,k1_funct_1(sK4,sK6(sK2,sK3,sK4)),sK9(sK2,sK3,sK4)) | ~m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK0)) | (~spl10_1 | ~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_29 | ~spl10_30 | ~spl10_33 | ~spl10_41)),
% 0.21/0.52    inference(resolution,[],[f546,f507])).
% 0.21/0.52  fof(f507,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1)) | r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl10_1 | ~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_29 | ~spl10_30 | ~spl10_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f506,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    l1_orders_2(sK0) | ~spl10_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl10_1 <=> l1_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.52  fof(f506,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1)) | ~r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | (~spl10_2 | ~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_29 | ~spl10_30 | ~spl10_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f505,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    l1_orders_2(sK1) | ~spl10_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl10_2 <=> l1_orders_2(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.52  fof(f505,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1)) | ~r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK1) | ~l1_orders_2(sK0)) ) | (~spl10_5 | ~spl10_7 | ~spl10_10 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_29 | ~spl10_30 | ~spl10_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f504,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl10_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl10_10 <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.52  fof(f504,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1)) | ~r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~l1_orders_2(sK0)) ) | (~spl10_5 | ~spl10_7 | ~spl10_12 | ~spl10_17 | ~spl10_19 | ~spl10_29 | ~spl10_30 | ~spl10_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f503,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl10_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl10_12 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.52  fof(f503,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1)) | ~r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~l1_orders_2(sK0)) ) | (~spl10_5 | ~spl10_7 | ~spl10_17 | ~spl10_19 | ~spl10_29 | ~spl10_30 | ~spl10_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f502,f403])).
% 0.21/0.52  fof(f403,plain,(
% 0.21/0.52    m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK1)) | (~spl10_19 | ~spl10_33)),
% 0.21/0.52    inference(superposition,[],[f180,f336])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK3) | ~spl10_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f334])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    spl10_33 <=> u1_struct_0(sK1) = u1_struct_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK3)) | ~spl10_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl10_19 <=> m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.52  fof(f502,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1)) | ~r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~l1_orders_2(sK0)) ) | (~spl10_5 | ~spl10_7 | ~spl10_17 | ~spl10_29 | ~spl10_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f501,f352])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK0)) | (~spl10_17 | ~spl10_30)),
% 0.21/0.52    inference(superposition,[],[f168,f313])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(sK2) | ~spl10_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    spl10_30 <=> u1_struct_0(sK0) = u1_struct_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK2)) | ~spl10_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl10_17 <=> m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.52  fof(f501,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK1,k1_funct_1(sK4,X0),sK9(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X0),u1_struct_0(sK1)) | ~r1_orders_2(sK0,X0,sK7(sK2,sK3,sK4)) | ~m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~l1_orders_2(sK0)) ) | (~spl10_5 | ~spl10_7 | ~spl10_29)),
% 0.21/0.52    inference(resolution,[],[f272,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    v5_orders_3(sK4,sK0,sK1) | ~spl10_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl10_7 <=> v5_orders_3(sK4,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v5_orders_3(sK4,X2,X0) | r1_orders_2(X0,k1_funct_1(sK4,X1),sK9(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X1),u1_struct_0(X0)) | ~r1_orders_2(X2,X1,sK7(sK2,sK3,sK4)) | ~m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~l1_orders_2(X2)) ) | (~spl10_5 | ~spl10_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f271,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    v1_funct_1(sK4) | ~spl10_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl10_5 <=> v1_funct_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(X0)) | r1_orders_2(X0,k1_funct_1(sK4,X1),sK9(sK2,sK3,sK4)) | ~m1_subset_1(k1_funct_1(sK4,X1),u1_struct_0(X0)) | ~r1_orders_2(X2,X1,sK7(sK2,sK3,sK4)) | ~m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~v5_orders_3(sK4,X2,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(sK4) | ~l1_orders_2(X0) | ~l1_orders_2(X2)) ) | ~spl10_29),
% 0.21/0.52    inference(superposition,[],[f60,f267])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    sK9(sK2,sK3,sK4) = k1_funct_1(sK4,sK7(sK2,sK3,sK4)) | ~spl10_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f265])).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    spl10_29 <=> sK9(sK2,sK3,sK4) = k1_funct_1(sK4,sK7(sK2,sK3,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X8,X7,X1] : (~m1_subset_1(k1_funct_1(X2,X8),u1_struct_0(X1)) | r1_orders_2(X1,k1_funct_1(X2,X7),k1_funct_1(X2,X8)) | ~m1_subset_1(k1_funct_1(X2,X7),u1_struct_0(X1)) | ~r1_orders_2(X0,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X0)) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~v5_orders_3(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X8,X7,X1,X9] : (r1_orders_2(X1,X9,k1_funct_1(X2,X8)) | k1_funct_1(X2,X7) != X9 | ~m1_subset_1(k1_funct_1(X2,X8),u1_struct_0(X1)) | ~m1_subset_1(X9,u1_struct_0(X1)) | ~r1_orders_2(X0,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X0)) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~v5_orders_3(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X10,X8,X7,X1,X9] : (r1_orders_2(X1,X9,X10) | k1_funct_1(X2,X8) != X10 | k1_funct_1(X2,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X1)) | ~m1_subset_1(X9,u1_struct_0(X1)) | ~r1_orders_2(X0,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X0)) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~v5_orders_3(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_orders_3(X2,X0,X1) | ((((~r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2)) & k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2) & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) & r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X1,X9,X10) | k1_funct_1(X2,X8) != X10 | k1_funct_1(X2,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X1))) | ~m1_subset_1(X9,u1_struct_0(X1))) | ~r1_orders_2(X0,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) | ~m1_subset_1(X7,u1_struct_0(X0))) | ~v5_orders_3(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f23,f27,f26,f25,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,sK6(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,sK6(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,sK6(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,sK6(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X0))) => (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,sK7(X0,X1,X2)) = X6 & k1_funct_1(X2,sK6(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,sK7(X0,X1,X2)) = X6 & k1_funct_1(X2,sK6(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (~r1_orders_2(X1,sK8(X0,X1,X2),X6) & k1_funct_1(X2,sK7(X0,X1,X2)) = X6 & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X6] : (~r1_orders_2(X1,sK8(X0,X1,X2),X6) & k1_funct_1(X2,sK7(X0,X1,X2)) = X6 & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X1))) => (~r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2)) & k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2) & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_orders_3(X2,X0,X1) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X1,X9,X10) | k1_funct_1(X2,X8) != X10 | k1_funct_1(X2,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X1))) | ~m1_subset_1(X9,u1_struct_0(X1))) | ~r1_orders_2(X0,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X0))) | ~m1_subset_1(X7,u1_struct_0(X0))) | ~v5_orders_3(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(rectify,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_orders_3(X2,X0,X1) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v5_orders_3(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : ((! [X5] : (! [X6] : ((r1_orders_2(X1,X5,X6) | (k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5)) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_orders_3(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_orders_2(X0,X3,X4) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X1)) => ((k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5) => r1_orders_2(X1,X5,X6)))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_3)).
% 0.21/0.52  fof(f546,plain,(
% 0.21/0.52    r1_orders_2(sK0,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)) | ~spl10_41),
% 0.21/0.52    inference(avatar_component_clause,[],[f544])).
% 0.21/0.52  fof(f544,plain,(
% 0.21/0.52    spl10_41 <=> r1_orders_2(sK0,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.21/0.52  fof(f547,plain,(
% 0.21/0.52    spl10_41 | ~spl10_1 | ~spl10_34 | ~spl10_36 | ~spl10_37),
% 0.21/0.52    inference(avatar_split_clause,[],[f525,f509,f479,f441,f65,f544])).
% 0.21/0.52  fof(f441,plain,(
% 0.21/0.52    spl10_34 <=> r2_hidden(k4_tarski(sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)),u1_orders_2(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 0.21/0.52  fof(f509,plain,(
% 0.21/0.52    spl10_37 <=> m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.21/0.52  fof(f525,plain,(
% 0.21/0.52    r1_orders_2(sK0,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)) | (~spl10_1 | ~spl10_34 | ~spl10_36 | ~spl10_37)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f67,f481,f443,f511,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f13])).
% 0.21/0.52  % (30315)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.52  fof(f511,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK0)) | ~spl10_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f509])).
% 0.21/0.52  fof(f443,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)),u1_orders_2(sK0)) | ~spl10_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f441])).
% 0.21/0.52  fof(f537,plain,(
% 0.21/0.52    ~spl10_40 | ~spl10_2 | ~spl10_18 | ~spl10_19 | ~spl10_33 | spl10_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f453,f446,f334,f178,f171,f70,f534])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    spl10_18 <=> m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.52  fof(f446,plain,(
% 0.21/0.52    spl10_35 <=> r2_hidden(k4_tarski(sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)),u1_orders_2(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.21/0.52  fof(f453,plain,(
% 0.21/0.52    ~r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) | (~spl10_2 | ~spl10_18 | ~spl10_19 | ~spl10_33 | spl10_35)),
% 0.21/0.52    inference(subsumption_resolution,[],[f452,f72])).
% 0.21/0.52  fof(f452,plain,(
% 0.21/0.52    ~r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) | ~l1_orders_2(sK1) | (~spl10_18 | ~spl10_19 | ~spl10_33 | spl10_35)),
% 0.21/0.52    inference(subsumption_resolution,[],[f451,f402])).
% 0.21/0.52  fof(f402,plain,(
% 0.21/0.52    m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1)) | (~spl10_18 | ~spl10_33)),
% 0.21/0.52    inference(superposition,[],[f173,f336])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK3)) | ~spl10_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f171])).
% 0.21/0.52  fof(f451,plain,(
% 0.21/0.52    ~r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) | ~m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1)) | ~l1_orders_2(sK1) | (~spl10_19 | ~spl10_33 | spl10_35)),
% 0.21/0.52    inference(subsumption_resolution,[],[f450,f403])).
% 0.21/0.52  fof(f450,plain,(
% 0.21/0.52    ~r1_orders_2(sK1,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) | ~m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK1)) | ~m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK1)) | ~l1_orders_2(sK1) | spl10_35),
% 0.21/0.52    inference(resolution,[],[f448,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f448,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)),u1_orders_2(sK1)) | spl10_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f446])).
% 0.21/0.52  fof(f517,plain,(
% 0.21/0.52    spl10_38 | ~spl10_18 | ~spl10_33),
% 0.21/0.52    inference(avatar_split_clause,[],[f402,f334,f171,f514])).
% 0.21/0.52  fof(f512,plain,(
% 0.21/0.52    spl10_37 | ~spl10_17 | ~spl10_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f352,f311,f166,f509])).
% 0.21/0.52  fof(f482,plain,(
% 0.21/0.52    spl10_36 | ~spl10_16 | ~spl10_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f351,f311,f153,f479])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl10_16 <=> m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK0)) | (~spl10_16 | ~spl10_30)),
% 0.21/0.52    inference(superposition,[],[f155,f313])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK2)) | ~spl10_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f449,plain,(
% 0.21/0.52    ~spl10_35 | ~spl10_4 | ~spl10_15 | ~spl10_18 | ~spl10_19 | ~spl10_21 | spl10_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f249,f242,f194,f178,f171,f136,f80,f446])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl10_4 <=> l1_orders_2(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    spl10_15 <=> g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    spl10_21 <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    spl10_25 <=> r1_orders_2(sK3,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)),u1_orders_2(sK1)) | (~spl10_4 | ~spl10_15 | ~spl10_18 | ~spl10_19 | ~spl10_21 | spl10_25)),
% 0.21/0.52    inference(forward_demodulation,[],[f248,f212])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    u1_orders_2(sK1) = u1_orders_2(sK3) | (~spl10_15 | ~spl10_21)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f138,f196,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) | ~spl10_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f194])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | ~spl10_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f136])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)),u1_orders_2(sK3)) | (~spl10_4 | ~spl10_18 | ~spl10_19 | spl10_25)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f82,f173,f180,f244,f56])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ~r1_orders_2(sK3,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) | spl10_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f242])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    l1_orders_2(sK3) | ~spl10_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f444,plain,(
% 0.21/0.52    spl10_34 | ~spl10_3 | ~spl10_14 | ~spl10_16 | ~spl10_17 | ~spl10_20 | ~spl10_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f247,f237,f189,f166,f153,f131,f75,f441])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl10_3 <=> l1_orders_2(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl10_14 <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    spl10_20 <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    spl10_24 <=> r1_orders_2(sK2,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)),u1_orders_2(sK0)) | (~spl10_3 | ~spl10_14 | ~spl10_16 | ~spl10_17 | ~spl10_20 | ~spl10_24)),
% 0.21/0.52    inference(forward_demodulation,[],[f246,f208])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    u1_orders_2(sK0) = u1_orders_2(sK2) | (~spl10_14 | ~spl10_20)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f133,f191,f58])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl10_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f189])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) | ~spl10_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)),u1_orders_2(sK2)) | (~spl10_3 | ~spl10_16 | ~spl10_17 | ~spl10_24)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f155,f168,f239,f55])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    r1_orders_2(sK2,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)) | ~spl10_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f237])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    l1_orders_2(sK2) | ~spl10_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f337,plain,(
% 0.21/0.52    spl10_33 | ~spl10_15 | ~spl10_21),
% 0.21/0.52    inference(avatar_split_clause,[],[f213,f194,f136,f334])).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK3) | (~spl10_15 | ~spl10_21)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f138,f196,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    spl10_30 | ~spl10_14 | ~spl10_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f209,f189,f131,f311])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(sK2) | (~spl10_14 | ~spl10_20)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f133,f191,f57])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    spl10_29 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f163,f126,f116,f106,f85,f80,f75,f265])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl10_9 <=> v5_orders_3(sK4,sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl10_11 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl10_13 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    sK9(sK2,sK3,sK4) = k1_funct_1(sK4,sK7(sK2,sK3,sK4)) | (~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_orders_3(X2,X0,X1) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~spl10_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl10_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f116])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~v5_orders_3(sK4,sK2,sK3) | spl10_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    spl10_26 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f161,f126,f116,f106,f85,f80,f75,f251])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    sK8(sK2,sK3,sK4) = k1_funct_1(sK4,sK6(sK2,sK3,sK4)) | (~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_orders_3(X2,X0,X1) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ~spl10_25 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f160,f126,f116,f106,f85,f80,f75,f242])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~r1_orders_2(sK3,sK8(sK2,sK3,sK4),sK9(sK2,sK3,sK4)) | (~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2)) | v5_orders_3(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    spl10_24 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f159,f126,f116,f106,f85,f80,f75,f237])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    r1_orders_2(sK2,sK6(sK2,sK3,sK4),sK7(sK2,sK3,sK4)) | (~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) | v5_orders_3(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    spl10_21 | ~spl10_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f141,f70,f194])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) | ~spl10_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f72,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    spl10_20 | ~spl10_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f140,f65,f189])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl10_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f67,f45])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    spl10_19 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f157,f126,f116,f106,f85,f80,f75,f178])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK3)) | (~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_orders_3(X2,X0,X1) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    spl10_18 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f150,f126,f116,f106,f85,f80,f75,f171])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK3)) | (~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_orders_3(X2,X0,X1) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    spl10_17 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f148,f126,f116,f106,f85,f80,f75,f166])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK2,sK3,sK4),u1_struct_0(sK2)) | (~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_orders_3(X2,X0,X1) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl10_16 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f146,f126,f116,f106,f85,f80,f75,f153])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    m1_subset_1(sK6(sK2,sK3,sK4),u1_struct_0(sK2)) | (~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_9 | ~spl10_11 | ~spl10_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f82,f87,f108,f118,f128,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_orders_3(X2,X0,X1) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl10_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f136])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    (((((~v5_orders_3(sK5,sK2,sK3) & v5_orders_3(sK4,sK0,sK1) & sK4 = sK5 & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & l1_orders_2(sK3)) & l1_orders_2(sK2)) & l1_orders_2(sK1)) & l1_orders_2(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f20,f19,f18,f17,f16,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK0,sK1) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK0,sK1) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) => (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK2,X3) & v5_orders_3(X4,sK0,sK1) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK2,X3) & v5_orders_3(X4,sK0,sK1) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & l1_orders_2(X3)) => (? [X4] : (? [X5] : (~v5_orders_3(X5,sK2,sK3) & v5_orders_3(X4,sK0,sK1) & X4 = X5 & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & l1_orders_2(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X4] : (? [X5] : (~v5_orders_3(X5,sK2,sK3) & v5_orders_3(X4,sK0,sK1) & X4 = X5 & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (~v5_orders_3(X5,sK2,sK3) & v5_orders_3(sK4,sK0,sK1) & sK4 = X5 & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X5] : (~v5_orders_3(X5,sK2,sK3) & v5_orders_3(sK4,sK0,sK1) & sK4 = X5 & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X5)) => (~v5_orders_3(sK5,sK2,sK3) & v5_orders_3(sK4,sK0,sK1) & sK4 = sK5 & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK5))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~v5_orders_3(X5,X2,X3) & (v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : (l1_orders_2(X2) => ! [X3] : (l1_orders_2(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_waybel_9)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl10_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f131])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl10_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f61,f126])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.21/0.52    inference(forward_demodulation,[],[f39,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    sK4 = sK5),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl10_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f121])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl10_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f62,f116])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.52    inference(forward_demodulation,[],[f38,f42])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl10_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f111])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~spl10_9 | ~spl10_6 | spl10_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f104,f100,f90,f106])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl10_6 <=> sK4 = sK5),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl10_8 <=> v5_orders_3(sK5,sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~v5_orders_3(sK4,sK2,sK3) | (~spl10_6 | spl10_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f102,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    sK4 = sK5 | ~spl10_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~v5_orders_3(sK5,sK2,sK3) | spl10_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f100])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~spl10_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f100])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~v5_orders_3(sK5,sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl10_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f95])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    v5_orders_3(sK4,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl10_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f90])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl10_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f63,f85])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(forward_demodulation,[],[f37,f42])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v1_funct_1(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl10_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f80])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    l1_orders_2(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl10_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f75])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    l1_orders_2(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl10_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f70])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    l1_orders_2(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl10_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f65])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    l1_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (30321)------------------------------
% 0.21/0.52  % (30321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30321)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (30321)Memory used [KB]: 11257
% 0.21/0.52  % (30321)Time elapsed: 0.025 s
% 0.21/0.52  % (30321)------------------------------
% 0.21/0.52  % (30321)------------------------------
% 0.21/0.52  % (30306)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (30297)Success in time 0.162 s
%------------------------------------------------------------------------------
