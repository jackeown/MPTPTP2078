%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t26_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:51 EDT 2019

% Result     : Theorem 12.19s
% Output     : Refutation 12.19s
% Verified   : 
% Statistics : Number of formulae       :  294 ( 663 expanded)
%              Number of leaves         :   60 ( 298 expanded)
%              Depth                    :   23
%              Number of atoms          : 1765 (4715 expanded)
%              Number of equality atoms :  195 ( 630 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162074,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f195,f202,f209,f216,f223,f230,f237,f244,f251,f307,f314,f338,f357,f369,f379,f393,f411,f425,f474,f555,f589,f597,f602,f610,f618,f630,f940,f1106,f1411,f1476,f2488,f2525,f3610,f3652,f19062,f23552,f23564,f161436,f162073])).

fof(f162073,plain,
    ( ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_98
    | spl10_193
    | ~ spl10_7270 ),
    inference(avatar_contradiction_clause,[],[f162072])).

fof(f162072,plain,
    ( $false
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_193
    | ~ spl10_7270 ),
    inference(subsumption_resolution,[],[f162071,f1407])).

fof(f1407,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_193 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f1406,plain,
    ( spl10_193
  <=> ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_193])])).

fof(f162071,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_7270 ),
    inference(forward_demodulation,[],[f162070,f609])).

fof(f609,plain,
    ( ! [X4] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k9_relat_1(sK2,X4)
    | ~ spl10_98 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl10_98
  <=> ! [X4] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k9_relat_1(sK2,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f162070,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_7270 ),
    inference(subsumption_resolution,[],[f162069,f229])).

fof(f229,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl10_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f162069,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_7270 ),
    inference(subsumption_resolution,[],[f162068,f337])).

fof(f337,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl10_40
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f162068,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl10_32
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_7270 ),
    inference(subsumption_resolution,[],[f162067,f356])).

fof(f356,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl10_44
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f162067,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl10_32
    | ~ spl10_58
    | ~ spl10_7270 ),
    inference(subsumption_resolution,[],[f162066,f424])).

fof(f424,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl10_58
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f162066,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl10_32
    | ~ spl10_7270 ),
    inference(resolution,[],[f161150,f306])).

fof(f306,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl10_32
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f161150,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK0,sK1)
        | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,sK4(sK0,sK1,sK2)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl10_7270 ),
    inference(avatar_component_clause,[],[f161149])).

fof(f161149,plain,
    ( spl10_7270
  <=> ! [X0] :
        ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0)
        | ~ v5_pre_topc(X0,sK0,sK1)
        | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,sK4(sK0,sK1,sK2)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7270])])).

fof(f161436,plain,
    ( spl10_7270
    | spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_48
    | ~ spl10_1758 ),
    inference(avatar_split_clause,[],[f153780,f19060,f377,f242,f221,f214,f207,f161149])).

fof(f207,plain,
    ( spl10_5
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f214,plain,
    ( spl10_6
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f221,plain,
    ( spl10_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f242,plain,
    ( spl10_14
  <=> v8_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f377,plain,
    ( spl10_48
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f19060,plain,
    ( spl10_1758
  <=> ! [X1,X0] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK4(sK0,sK1,sK2)),X0)
        | ~ v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ v8_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1758])])).

fof(f153780,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0)
        | ~ v5_pre_topc(X0,sK0,sK1)
        | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,sK4(sK0,sK1,sK2)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_48
    | ~ spl10_1758 ),
    inference(forward_demodulation,[],[f153779,f378])).

fof(f378,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f377])).

fof(f153779,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK0,sK1)
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,sK4(sK0,sK1,sK2)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_1758 ),
    inference(subsumption_resolution,[],[f153778,f208])).

fof(f208,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f207])).

fof(f153778,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK0,sK1)
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,sK4(sK0,sK1,sK2)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | v2_struct_0(sK1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_1758 ),
    inference(subsumption_resolution,[],[f153777,f215])).

fof(f215,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f153777,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK0,sK1)
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,sK4(sK0,sK1,sK2)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_1758 ),
    inference(subsumption_resolution,[],[f153776,f222])).

fof(f222,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f153776,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK0,sK1)
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,sK4(sK0,sK1,sK2)),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl10_14
    | ~ spl10_1758 ),
    inference(resolution,[],[f19061,f243])).

fof(f243,plain,
    ( v8_pre_topc(sK1)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f242])).

fof(f19061,plain,
    ( ! [X0,X1] :
        ( ~ v8_pre_topc(X0)
        | ~ v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK4(sK0,sK1,sK2)),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl10_1758 ),
    inference(avatar_component_clause,[],[f19060])).

fof(f23564,plain,
    ( ~ spl10_2
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_94
    | spl10_191
    | ~ spl10_434
    | ~ spl10_2212 ),
    inference(avatar_contradiction_clause,[],[f23563])).

fof(f23563,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_94
    | ~ spl10_191
    | ~ spl10_434
    | ~ spl10_2212 ),
    inference(subsumption_resolution,[],[f23562,f1401])).

fof(f1401,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_191 ),
    inference(avatar_component_clause,[],[f1400])).

fof(f1400,plain,
    ( spl10_191
  <=> ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_191])])).

fof(f23562,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_94
    | ~ spl10_434
    | ~ spl10_2212 ),
    inference(forward_demodulation,[],[f23561,f3609])).

fof(f3609,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))) = sK4(sK0,sK1,sK2)
    | ~ spl10_434 ),
    inference(avatar_component_clause,[],[f3608])).

fof(f3608,plain,
    ( spl10_434
  <=> k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))) = sK4(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_434])])).

fof(f23561,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_94
    | ~ spl10_2212 ),
    inference(forward_demodulation,[],[f23560,f601])).

fof(f601,plain,
    ( ! [X4] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k10_relat_1(sK2,X4)
    | ~ spl10_94 ),
    inference(avatar_component_clause,[],[f600])).

fof(f600,plain,
    ( spl10_94
  <=> ! [X4] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k10_relat_1(sK2,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f23560,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_2212 ),
    inference(subsumption_resolution,[],[f23559,f201])).

fof(f201,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl10_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f23559,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_10
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_2212 ),
    inference(subsumption_resolution,[],[f23558,f229])).

fof(f23558,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_2212 ),
    inference(subsumption_resolution,[],[f23557,f356])).

fof(f23557,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_32
    | ~ spl10_40
    | ~ spl10_2212 ),
    inference(subsumption_resolution,[],[f23556,f306])).

fof(f23556,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_40
    | ~ spl10_2212 ),
    inference(resolution,[],[f23551,f337])).

fof(f23551,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(X4),u1_struct_0(sK1),X5,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),X4)
        | ~ v1_funct_1(X5)
        | ~ l1_pre_topc(X4) )
    | ~ spl10_2212 ),
    inference(avatar_component_clause,[],[f23550])).

fof(f23550,plain,
    ( spl10_2212
  <=> ! [X5,X4] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X4),u1_struct_0(sK1),X5,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),X4)
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | ~ l1_pre_topc(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2212])])).

fof(f23552,plain,
    ( spl10_2212
    | ~ spl10_8
    | ~ spl10_104
    | ~ spl10_192 ),
    inference(avatar_split_clause,[],[f23000,f1409,f628,f221,f23550])).

fof(f628,plain,
    ( spl10_104
  <=> ! [X4] : m1_subset_1(k9_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f1409,plain,
    ( spl10_192
  <=> v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_192])])).

fof(f23000,plain,
    ( ! [X4,X5] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X4),u1_struct_0(sK1),X5,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),X4)
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | ~ l1_pre_topc(X4) )
    | ~ spl10_8
    | ~ spl10_104
    | ~ spl10_192 ),
    inference(subsumption_resolution,[],[f22999,f222])).

fof(f22999,plain,
    ( ! [X4,X5] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X4),u1_struct_0(sK1),X5,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),X4)
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X4) )
    | ~ spl10_104
    | ~ spl10_192 ),
    inference(subsumption_resolution,[],[f22993,f629])).

fof(f629,plain,
    ( ! [X4] : m1_subset_1(k9_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_104 ),
    inference(avatar_component_clause,[],[f628])).

fof(f22993,plain,
    ( ! [X4,X5] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X4),u1_struct_0(sK1),X5,k9_relat_1(sK2,sK4(sK0,sK1,sK2))),X4)
        | ~ m1_subset_1(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X4) )
    | ~ spl10_192 ),
    inference(resolution,[],[f1410,f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v4_pre_topc(X4,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
                    & v4_pre_topc(sK3(X0,X1,X2),X1)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f90,f91])).

fof(f91,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
        & v4_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',d12_pre_topc)).

fof(f1410,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_192 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f19062,plain,
    ( spl10_1758
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_12
    | ~ spl10_190
    | ~ spl10_442 ),
    inference(avatar_split_clause,[],[f19057,f3650,f1403,f235,f200,f193,f19060])).

fof(f193,plain,
    ( spl10_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f235,plain,
    ( spl10_12
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f1403,plain,
    ( spl10_190
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_190])])).

fof(f3650,plain,
    ( spl10_442
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_442])])).

fof(f19057,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK4(sK0,sK1,sK2)),X0)
        | ~ v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ v8_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_12
    | ~ spl10_190
    | ~ spl10_442 ),
    inference(subsumption_resolution,[],[f18753,f3651])).

fof(f3651,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_442 ),
    inference(avatar_component_clause,[],[f3650])).

fof(f18753,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK4(sK0,sK1,sK2)),X0)
        | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ v8_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_12
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f18752,f194])).

fof(f194,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f193])).

fof(f18752,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK4(sK0,sK1,sK2)),X0)
        | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ v8_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_2
    | ~ spl10_12
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f18751,f201])).

fof(f18751,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK4(sK0,sK1,sK2)),X0)
        | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ v8_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_12
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f18735,f236])).

fof(f236,plain,
    ( v1_compts_1(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f235])).

fof(f18735,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK4(sK0,sK1,sK2)),X0)
        | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_pre_topc(X1,sK0,X0)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ v8_pre_topc(X0)
        | ~ v1_compts_1(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_190 ),
    inference(resolution,[],[f1404,f143])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v8_pre_topc(X1)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',t25_compts_1)).

fof(f1404,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_190 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f3652,plain,
    ( spl10_442
    | ~ spl10_100
    | ~ spl10_434 ),
    inference(avatar_split_clause,[],[f3634,f3608,f616,f3650])).

fof(f616,plain,
    ( spl10_100
  <=> ! [X4] : m1_subset_1(k10_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f3634,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_100
    | ~ spl10_434 ),
    inference(superposition,[],[f617,f3609])).

fof(f617,plain,
    ( ! [X4] : m1_subset_1(k10_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_100 ),
    inference(avatar_component_clause,[],[f616])).

fof(f3610,plain,
    ( spl10_434
    | ~ spl10_154
    | ~ spl10_312 ),
    inference(avatar_split_clause,[],[f2526,f2523,f1104,f3608])).

fof(f1104,plain,
    ( spl10_154
  <=> ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f2523,plain,
    ( spl10_312
  <=> r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_312])])).

fof(f2526,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK4(sK0,sK1,sK2))) = sK4(sK0,sK1,sK2)
    | ~ spl10_154
    | ~ spl10_312 ),
    inference(resolution,[],[f2524,f1105])).

fof(f1105,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl10_154 ),
    inference(avatar_component_clause,[],[f1104])).

fof(f2524,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_312 ),
    inference(avatar_component_clause,[],[f2523])).

fof(f2525,plain,
    ( spl10_312
    | ~ spl10_2
    | spl10_5
    | ~ spl10_8
    | spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f2500,f2486,f423,f409,f377,f367,f355,f336,f312,f221,f207,f200,f2523])).

fof(f312,plain,
    ( spl10_35
  <=> ~ v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f367,plain,
    ( spl10_46
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f409,plain,
    ( spl10_54
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f2486,plain,
    ( spl10_306
  <=> ! [X1,X0] :
        ( v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | r1_tarski(sK4(X0,X1,sK2),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_306])])).

fof(f2500,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f2499,f410])).

fof(f410,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f409])).

fof(f2499,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_58
    | ~ spl10_306 ),
    inference(forward_demodulation,[],[f2498,f368])).

fof(f368,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f367])).

fof(f2498,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_58
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f2497,f378])).

fof(f2497,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_306 ),
    inference(forward_demodulation,[],[f2496,f424])).

fof(f2496,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f2495,f201])).

fof(f2495,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f2494,f208])).

fof(f2494,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f2493,f222])).

fof(f2493,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f2492,f313])).

fof(f313,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f312])).

fof(f2492,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f2491,f356])).

fof(f2491,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_40
    | ~ spl10_306 ),
    inference(resolution,[],[f2487,f337])).

fof(f2487,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v3_tops_2(sK2,X0,X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | r1_tarski(sK4(X0,X1,sK2),u1_struct_0(X0)) )
    | ~ spl10_306 ),
    inference(avatar_component_clause,[],[f2486])).

fof(f2488,plain,
    ( spl10_306
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f932,f249,f228,f2486])).

fof(f249,plain,
    ( spl10_16
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f932,plain,
    ( ! [X0,X1] :
        ( v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | r1_tarski(sK4(X0,X1,sK2),u1_struct_0(X0)) )
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f931,f229])).

fof(f931,plain,
    ( ! [X0,X1] :
        ( v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | r1_tarski(sK4(X0,X1,sK2),u1_struct_0(X0)) )
    | ~ spl10_16 ),
    inference(resolution,[],[f566,f250])).

fof(f250,plain,
    ( v2_funct_1(sK2)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f249])).

fof(f566,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X0)
      | v3_tops_2(X0,X1,X2)
      | k2_struct_0(X2) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0)
      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | r1_tarski(sK4(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f139,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',t3_subset)).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_2(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
                      | ~ v4_pre_topc(sK4(X0,X1,X2),X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
                      | v4_pre_topc(sK4(X0,X1,X2),X0) )
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f95,f96])).

fof(f96,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | ~ v4_pre_topc(X3,X0) )
          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | v4_pre_topc(X3,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
          | ~ v4_pre_topc(sK4(X0,X1,X2),X0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
          | v4_pre_topc(sK4(X0,X1,X2),X0) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ( ( v4_pre_topc(X3,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                            | ~ v4_pre_topc(X3,X0) ) )
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ( ( v4_pre_topc(X3,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                            | ~ v4_pre_topc(X3,X0) ) )
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',t72_tops_2)).

fof(f1476,plain,
    ( ~ spl10_193
    | ~ spl10_2
    | spl10_5
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1428,f1403,f608,f423,f409,f377,f367,f355,f336,f312,f249,f228,f221,f207,f200,f1406])).

fof(f1428,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1427,f410])).

fof(f1427,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_190 ),
    inference(forward_demodulation,[],[f1426,f368])).

fof(f1426,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1425,f378])).

fof(f1425,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_190 ),
    inference(forward_demodulation,[],[f1424,f424])).

fof(f1424,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_98
    | ~ spl10_190 ),
    inference(forward_demodulation,[],[f1423,f609])).

fof(f1423,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1422,f201])).

fof(f1422,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1421,f208])).

fof(f1421,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1420,f222])).

fof(f1420,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1419,f229])).

fof(f1419,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1418,f337])).

fof(f1418,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_44
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1417,f356])).

fof(f1417,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_16
    | ~ spl10_35
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1416,f250])).

fof(f1416,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_35
    | ~ spl10_190 ),
    inference(subsumption_resolution,[],[f1412,f313])).

fof(f1412,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_190 ),
    inference(resolution,[],[f1404,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
      | v3_tops_2(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f1411,plain,
    ( spl10_190
    | spl10_192
    | ~ spl10_2
    | spl10_5
    | ~ spl10_8
    | spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_134 ),
    inference(avatar_split_clause,[],[f955,f938,f608,f423,f409,f377,f367,f355,f336,f312,f221,f207,f200,f1409,f1403])).

fof(f938,plain,
    ( spl10_134
  <=> ! [X1,X0] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X1)
        | v4_pre_topc(sK4(X0,X1,sK2),X0)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f955,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_98
    | ~ spl10_134 ),
    inference(forward_demodulation,[],[f954,f609])).

fof(f954,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f953,f410])).

fof(f953,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_46
    | ~ spl10_48
    | ~ spl10_58
    | ~ spl10_134 ),
    inference(forward_demodulation,[],[f952,f368])).

fof(f952,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_58
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f951,f378])).

fof(f951,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_58
    | ~ spl10_134 ),
    inference(forward_demodulation,[],[f950,f424])).

fof(f950,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f949,f201])).

fof(f949,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f948,f208])).

fof(f948,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f947,f222])).

fof(f947,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_44
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f946,f356])).

fof(f946,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_35
    | ~ spl10_40
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f945,f313])).

fof(f945,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_40
    | ~ spl10_134 ),
    inference(resolution,[],[f939,f337])).

fof(f939,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v4_pre_topc(sK4(X0,X1,sK2),X0)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_134 ),
    inference(avatar_component_clause,[],[f938])).

fof(f1106,plain,
    ( spl10_154
    | ~ spl10_50
    | ~ spl10_66
    | ~ spl10_84 ),
    inference(avatar_split_clause,[],[f904,f553,f472,f391,f1104])).

fof(f391,plain,
    ( spl10_50
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f472,plain,
    ( spl10_66
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f553,plain,
    ( spl10_84
  <=> ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f904,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl10_50
    | ~ spl10_66
    | ~ spl10_84 ),
    inference(forward_demodulation,[],[f903,f473])).

fof(f473,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f472])).

fof(f903,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl10_50
    | ~ spl10_84 ),
    inference(subsumption_resolution,[],[f901,f392])).

fof(f392,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f391])).

fof(f901,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl10_84 ),
    inference(resolution,[],[f437,f554])).

fof(f554,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f553])).

fof(f437,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(resolution,[],[f145,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',d10_xboole_0)).

fof(f145,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',t146_funct_1)).

fof(f940,plain,
    ( spl10_134
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f572,f249,f228,f938])).

fof(f572,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X1)
        | v4_pre_topc(sK4(X0,X1,sK2),X0)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f571,f229])).

fof(f571,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X1)
        | v4_pre_topc(sK4(X0,X1,sK2),X0)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_16 ),
    inference(resolution,[],[f140,f250])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X1)
      | v4_pre_topc(sK4(X0,X1,X2),X0)
      | v3_tops_2(X2,X0,X1)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f630,plain,
    ( spl10_104
    | ~ spl10_88
    | ~ spl10_98 ),
    inference(avatar_split_clause,[],[f624,f608,f587,f628])).

fof(f587,plain,
    ( spl10_88
  <=> ! [X4] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f624,plain,
    ( ! [X4] : m1_subset_1(k9_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_88
    | ~ spl10_98 ),
    inference(backward_demodulation,[],[f609,f588])).

fof(f588,plain,
    ( ! [X4] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f587])).

fof(f618,plain,
    ( spl10_100
    | ~ spl10_92
    | ~ spl10_94 ),
    inference(avatar_split_clause,[],[f613,f600,f595,f616])).

fof(f595,plain,
    ( spl10_92
  <=> ! [X4] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f613,plain,
    ( ! [X4] : m1_subset_1(k10_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_92
    | ~ spl10_94 ),
    inference(backward_demodulation,[],[f601,f596])).

fof(f596,plain,
    ( ! [X4] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_92 ),
    inference(avatar_component_clause,[],[f595])).

fof(f610,plain,
    ( spl10_98
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f504,f355,f608])).

fof(f504,plain,
    ( ! [X4] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k9_relat_1(sK2,X4)
    | ~ spl10_44 ),
    inference(resolution,[],[f173,f356])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',redefinition_k7_relset_1)).

fof(f602,plain,
    ( spl10_94
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f500,f355,f600])).

fof(f500,plain,
    ( ! [X4] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k10_relat_1(sK2,X4)
    | ~ spl10_44 ),
    inference(resolution,[],[f172,f356])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',redefinition_k8_relset_1)).

fof(f597,plain,
    ( spl10_92
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f490,f355,f595])).

fof(f490,plain,
    ( ! [X4] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_44 ),
    inference(resolution,[],[f171,f356])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',dt_k8_relset_1)).

fof(f589,plain,
    ( spl10_88
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f485,f355,f587])).

fof(f485,plain,
    ( ! [X4] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_44 ),
    inference(resolution,[],[f170,f356])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',dt_k7_relset_1)).

fof(f555,plain,
    ( spl10_84
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f447,f391,f249,f228,f553])).

fof(f447,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_50 ),
    inference(subsumption_resolution,[],[f446,f392])).

fof(f446,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f445,f229])).

fof(f445,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_16 ),
    inference(resolution,[],[f149,f250])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',t152_funct_1)).

fof(f474,plain,
    ( spl10_66
    | ~ spl10_44
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f463,f409,f355,f472])).

fof(f463,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl10_44
    | ~ spl10_54 ),
    inference(forward_demodulation,[],[f461,f410])).

fof(f461,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl10_44 ),
    inference(resolution,[],[f159,f356])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',redefinition_k1_relset_1)).

fof(f425,plain,
    ( spl10_58
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f397,f377,f423])).

fof(f397,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f121,f378])).

fof(f121,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    & v5_pre_topc(sK2,sK0,sK1)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    & v8_pre_topc(sK1)
    & v1_compts_1(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f87,f86,f85])).

fof(f85,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(X2,X0,X1)
                & v5_pre_topc(X2,X0,X1)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,sK0,X1)
              & v5_pre_topc(X2,sK0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0)
              & v8_pre_topc(X1)
              & v1_compts_1(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ v3_tops_2(X2,X0,sK1)
            & v5_pre_topc(X2,X0,sK1)
            & v2_funct_1(X2)
            & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(X0)
            & v8_pre_topc(sK1)
            & v1_compts_1(X0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_tops_2(X2,X0,X1)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
          & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
          & v8_pre_topc(X1)
          & v1_compts_1(X0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v3_tops_2(sK2,X0,X1)
        & v5_pre_topc(sK2,X0,X1)
        & v2_funct_1(sK2)
        & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X0)
        & v8_pre_topc(X1)
        & v1_compts_1(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',t26_compts_1)).

fof(f411,plain,
    ( spl10_54
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f395,f367,f409])).

fof(f395,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl10_46 ),
    inference(forward_demodulation,[],[f120,f368])).

fof(f120,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f393,plain,
    ( spl10_50
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f385,f355,f391])).

fof(f385,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_44 ),
    inference(resolution,[],[f157,f356])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',cc1_relset_1)).

fof(f379,plain,
    ( spl10_48
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f359,f221,f377])).

fof(f359,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl10_8 ),
    inference(resolution,[],[f340,f222])).

fof(f340,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f126,f129])).

fof(f129,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',dt_l1_pre_topc)).

fof(f126,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t26_compts_1.p',d3_struct_0)).

fof(f369,plain,
    ( spl10_46
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f358,f200,f367])).

fof(f358,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl10_2 ),
    inference(resolution,[],[f340,f201])).

fof(f357,plain,(
    spl10_44 ),
    inference(avatar_split_clause,[],[f117,f355])).

fof(f117,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f88])).

fof(f338,plain,(
    spl10_40 ),
    inference(avatar_split_clause,[],[f116,f336])).

fof(f116,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

fof(f314,plain,(
    ~ spl10_35 ),
    inference(avatar_split_clause,[],[f124,f312])).

fof(f124,plain,(
    ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f307,plain,(
    spl10_32 ),
    inference(avatar_split_clause,[],[f123,f305])).

fof(f123,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f251,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f122,f249])).

fof(f122,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

fof(f244,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f119,f242])).

fof(f119,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f237,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f118,f235])).

fof(f118,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f230,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f115,f228])).

fof(f115,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

fof(f223,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f114,f221])).

fof(f114,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f216,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f113,f214])).

fof(f113,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f209,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f112,f207])).

fof(f112,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f202,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f111,f200])).

fof(f111,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f195,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f110,f193])).

fof(f110,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).
%------------------------------------------------------------------------------
