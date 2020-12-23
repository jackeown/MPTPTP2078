%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1832+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:41 EST 2020

% Result     : Theorem 3.72s
% Output     : Refutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  402 (1167 expanded)
%              Number of leaves         :   60 ( 538 expanded)
%              Depth                    :   31
%              Number of atoms          : 4751 (13827 expanded)
%              Number of equality atoms :   50 (  73 expanded)
%              Maximal formula depth    :   30 (  12 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f198,f203,f208,f261,f265,f297,f462,f489,f510,f532,f538,f542,f549,f717,f728,f793,f819,f841,f865,f1170,f1180,f1807,f1877,f1893,f2092,f2108,f2223,f2238,f2239])).

fof(f2239,plain,
    ( sK5 != k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v5_pre_topc(sK5,sK3,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2238,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_166 ),
    inference(avatar_contradiction_clause,[],[f2237])).

fof(f2237,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2236,f107])).

fof(f107,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f2236,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2235,f112])).

fof(f112,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f2235,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2234,f117])).

fof(f117,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f2234,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2233,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2233,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2232,f127])).

fof(f127,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2232,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2231,f132])).

fof(f132,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f2231,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2230,f1165])).

fof(f1165,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f1164,plain,
    ( spl6_102
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f2230,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2229,f172])).

fof(f172,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_14
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f2229,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2228,f247])).

fof(f247,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl6_27
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f2228,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | ~ spl6_30
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2227,f251])).

fof(f251,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl6_28
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f2227,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_30
    | spl6_166 ),
    inference(subsumption_resolution,[],[f2225,f259])).

fof(f259,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl6_30
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f2225,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_166 ),
    inference(resolution,[],[f2091,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f2091,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl6_166 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2089,plain,
    ( spl6_166
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).

fof(f2223,plain,
    ( ~ spl6_166
    | spl6_173
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_50
    | ~ spl6_79
    | ~ spl6_164 ),
    inference(avatar_split_clause,[],[f2202,f2081,f862,f535,f205,f195,f150,f2220,f2089])).

fof(f2220,plain,
    ( spl6_173
  <=> sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_173])])).

fof(f150,plain,
    ( spl6_10
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f195,plain,
    ( spl6_19
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f205,plain,
    ( spl6_21
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f535,plain,
    ( spl6_50
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f862,plain,
    ( spl6_79
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f2081,plain,
    ( spl6_164
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_164])])).

fof(f2202,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_50
    | ~ spl6_79
    | ~ spl6_164 ),
    inference(subsumption_resolution,[],[f907,f2082])).

fof(f2082,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_164 ),
    inference(avatar_component_clause,[],[f2081])).

fof(f907,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_50
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f906,f537])).

fof(f537,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f535])).

fof(f906,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f905,f152])).

fof(f152,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f905,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f904,f197])).

fof(f197,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f904,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_21
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f872,f207])).

fof(f207,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f872,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_79 ),
    inference(resolution,[],[f864,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f864,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f862])).

fof(f2108,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_164 ),
    inference(avatar_contradiction_clause,[],[f2107])).

fof(f2107,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2106,f107])).

fof(f2106,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2105,f112])).

fof(f2105,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2104,f117])).

fof(f2104,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2103,f122])).

fof(f2103,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2102,f127])).

fof(f2102,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2101,f132])).

fof(f2101,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2100,f1165])).

fof(f2100,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2099,f172])).

fof(f2099,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2098,f247])).

fof(f2098,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | ~ spl6_30
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2097,f251])).

fof(f2097,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_30
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2095,f259])).

fof(f2095,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_164 ),
    inference(resolution,[],[f2083,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2083,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_164 ),
    inference(avatar_component_clause,[],[f2081])).

fof(f2092,plain,
    ( ~ spl6_164
    | ~ spl6_165
    | ~ spl6_166
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_156 ),
    inference(avatar_split_clause,[],[f2076,f1870,f535,f529,f258,f254,f250,f246,f200,f190,f180,f170,f165,f160,f155,f140,f135,f130,f125,f120,f115,f110,f105,f2089,f2085,f2081])).

fof(f2085,plain,
    ( spl6_165
  <=> v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_165])])).

fof(f135,plain,
    ( spl6_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f140,plain,
    ( spl6_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f155,plain,
    ( spl6_11
  <=> v1_borsuk_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f160,plain,
    ( spl6_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f165,plain,
    ( spl6_13
  <=> v1_borsuk_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f180,plain,
    ( spl6_16
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f190,plain,
    ( spl6_18
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f200,plain,
    ( spl6_20
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f254,plain,
    ( spl6_29
  <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f529,plain,
    ( spl6_49
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f1870,plain,
    ( spl6_156
  <=> sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_156])])).

fof(f2076,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_156 ),
    inference(subsumption_resolution,[],[f2075,f192])).

fof(f192,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f2075,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_20
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_156 ),
    inference(forward_demodulation,[],[f2074,f1872])).

fof(f1872,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_156 ),
    inference(avatar_component_clause,[],[f1870])).

fof(f2074,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_20
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_156 ),
    inference(subsumption_resolution,[],[f2073,f182])).

fof(f182,plain,
    ( v5_pre_topc(sK4,sK2,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f2073,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_156 ),
    inference(forward_demodulation,[],[f2072,f1872])).

fof(f2072,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_156 ),
    inference(subsumption_resolution,[],[f2071,f202])).

fof(f202,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f200])).

fof(f2071,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_156 ),
    inference(forward_demodulation,[],[f2070,f1872])).

fof(f2070,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f569,f259])).

fof(f569,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f568,f107])).

fof(f568,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f567,f112])).

fof(f567,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f566,f117])).

fof(f566,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f565,f122])).

fof(f565,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f564,f127])).

fof(f564,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f563,f132])).

fof(f563,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f562,f137])).

fof(f137,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f562,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f561,f157])).

fof(f157,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f561,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f560,f162])).

fof(f162,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f560,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f559,f142])).

fof(f142,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f559,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f558,f167])).

fof(f167,plain,
    ( v1_borsuk_1(sK3,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f558,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_borsuk_1(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f557,f172])).

fof(f557,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_27
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f556,f247])).

fof(f556,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f555,f251])).

fof(f555,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_29
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f554,f531])).

fof(f531,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f529])).

fof(f554,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_29
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f550,f256])).

fof(f256,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f254])).

fof(f550,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_50 ),
    inference(resolution,[],[f537,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_borsuk_1(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_tmap_1)).

fof(f1893,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_157 ),
    inference(avatar_contradiction_clause,[],[f1892])).

fof(f1892,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1891,f107])).

fof(f1891,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1890,f112])).

fof(f1890,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1889,f117])).

fof(f1889,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1888,f122])).

fof(f1888,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1887,f127])).

fof(f1887,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1886,f132])).

fof(f1886,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_102
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1885,f1165])).

fof(f1885,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1884,f162])).

fof(f1884,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1883,f247])).

fof(f1883,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | ~ spl6_30
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1882,f251])).

fof(f1882,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_30
    | spl6_157 ),
    inference(subsumption_resolution,[],[f1879,f259])).

fof(f1879,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_157 ),
    inference(resolution,[],[f1876,f85])).

fof(f1876,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_157 ),
    inference(avatar_component_clause,[],[f1874])).

fof(f1874,plain,
    ( spl6_157
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_157])])).

fof(f1877,plain,
    ( spl6_156
    | ~ spl6_157
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(avatar_split_clause,[],[f1828,f1168,f529,f258,f250,f246,f205,f200,f195,f190,f150,f145,f130,f125,f120,f1874,f1870])).

fof(f145,plain,
    ( spl6_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1168,plain,
    ( spl6_103
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0))
        | ~ v1_funct_2(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))
        | ~ m1_subset_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)),u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X2))
        | k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)) = X1
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f1828,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1827,f192])).

fof(f1827,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1826,f147])).

fof(f147,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f1826,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1825,f202])).

fof(f1825,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1824,f207])).

fof(f1824,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1823,f132])).

fof(f1823,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1822,f127])).

fof(f1822,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1821,f122])).

fof(f1821,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1820,f197])).

fof(f1820,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_49
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1819,f531])).

fof(f1819,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1818,f152])).

fof(f1818,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_30
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1817,f251])).

fof(f1817,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_27
    | ~ spl6_30
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f1811,f247])).

fof(f1811,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_30
    | ~ spl6_103 ),
    inference(resolution,[],[f259,f1169])).

fof(f1169,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))))
        | ~ v1_funct_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0))
        | ~ v1_funct_2(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)),u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X2))
        | k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)) = X1
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X2)) )
    | ~ spl6_103 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f1807,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(avatar_contradiction_clause,[],[f1806])).

fof(f1806,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1805,f107])).

fof(f1805,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1804,f112])).

fof(f1804,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1803,f117])).

fof(f1803,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1802,f122])).

fof(f1802,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1801,f127])).

fof(f1801,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1800,f132])).

fof(f1800,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1799,f137])).

fof(f1799,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1798,f162])).

fof(f1798,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1797,f142])).

fof(f1797,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1796,f172])).

fof(f1796,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1795,f147])).

fof(f1795,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1794,f192])).

fof(f1794,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1793,f202])).

fof(f1793,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1792,f152])).

fof(f1792,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_19
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1791,f197])).

fof(f1791,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1789,f207])).

fof(f1789,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_30 ),
    inference(resolution,[],[f260,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f260,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f258])).

fof(f1180,plain,
    ( spl6_1
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | spl6_102 ),
    inference(avatar_contradiction_clause,[],[f1179])).

fof(f1179,plain,
    ( $false
    | spl6_1
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | spl6_102 ),
    inference(subsumption_resolution,[],[f1178,f107])).

fof(f1178,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | spl6_102 ),
    inference(subsumption_resolution,[],[f1177,f117])).

fof(f1177,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | spl6_102 ),
    inference(subsumption_resolution,[],[f1176,f137])).

fof(f1176,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | spl6_102 ),
    inference(subsumption_resolution,[],[f1175,f162])).

fof(f1175,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_14
    | spl6_102 ),
    inference(subsumption_resolution,[],[f1174,f142])).

fof(f1174,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | spl6_102 ),
    inference(subsumption_resolution,[],[f1172,f172])).

fof(f1172,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_102 ),
    inference(resolution,[],[f1166,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f1166,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | spl6_102 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f1170,plain,
    ( ~ spl6_102
    | spl6_103
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_75 ),
    inference(avatar_split_clause,[],[f830,f817,f160,f115,f110,f105,f1168,f1164])).

fof(f817,plain,
    ( spl6_75
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)) = X2
        | ~ m1_subset_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f830,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)) = X1
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ v1_funct_2(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)),u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)))
        | ~ m1_subset_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))
        | ~ v1_funct_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_75 ),
    inference(subsumption_resolution,[],[f829,f107])).

fof(f829,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)) = X1
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ v1_funct_2(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)),u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)))
        | ~ m1_subset_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))
        | ~ v1_funct_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_75 ),
    inference(subsumption_resolution,[],[f828,f112])).

fof(f828,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)) = X1
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ v1_funct_2(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)),u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)))
        | ~ m1_subset_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))
        | ~ v1_funct_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_75 ),
    inference(subsumption_resolution,[],[f827,f117])).

fof(f827,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)) = X1
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ v1_funct_2(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)),u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)))
        | ~ m1_subset_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))
        | ~ v1_funct_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_75 ),
    inference(subsumption_resolution,[],[f826,f162])).

fof(f826,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)) = X1
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ v1_funct_2(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)),u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)))
        | ~ m1_subset_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))
        | ~ v1_funct_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0))
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_75 ),
    inference(duplicate_literal_removal,[],[f825])).

fof(f825,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)) = X1
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X2))
        | ~ v1_funct_2(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)),u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(k3_tmap_1(sK0,X2,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X2,sK2,sK3,X1,X0)))
        | ~ m1_subset_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X2))
        | ~ v1_funct_1(k10_tmap_1(sK0,X2,sK2,sK3,X1,X0))
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_75 ),
    inference(resolution,[],[f818,f86])).

fof(f818,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)) = X2
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_2(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) )
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f817])).

fof(f865,plain,
    ( spl6_79
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f850,f839,f205,f195,f150,f862])).

fof(f839,plain,
    ( spl6_76
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f850,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f849,f152])).

fof(f849,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ v1_funct_1(sK5)
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f847,f197])).

fof(f847,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ v1_funct_1(sK5)
    | ~ spl6_21
    | ~ spl6_76 ),
    inference(resolution,[],[f840,f207])).

fof(f840,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
        | ~ v1_funct_1(X0) )
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f839])).

fof(f841,plain,
    ( spl6_76
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_72 ),
    inference(avatar_split_clause,[],[f808,f791,f200,f190,f145,f839])).

fof(f791,plain,
    ( spl6_72
  <=> ! [X3,X2] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f808,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) )
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f807,f147])).

fof(f807,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) )
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f805,f192])).

fof(f805,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) )
    | ~ spl6_20
    | ~ spl6_72 ),
    inference(resolution,[],[f792,f202])).

fof(f792,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) )
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f791])).

fof(f819,plain,
    ( spl6_75
    | ~ spl6_65 ),
    inference(avatar_split_clause,[],[f744,f726,f817])).

fof(f726,plain,
    ( spl6_65
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f744,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)) = X2
        | ~ m1_subset_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) )
    | ~ spl6_65 ),
    inference(duplicate_literal_removal,[],[f743])).

fof(f743,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) )
    | ~ spl6_65 ),
    inference(resolution,[],[f727,f82])).

fof(f727,plain,
    ( ! [X2,X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f726])).

fof(f793,plain,
    ( spl6_72
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f738,f715,f130,f125,f120,f791])).

fof(f715,plain,
    ( spl6_64
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f738,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f737,f122])).

fof(f737,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f734,f127])).

fof(f734,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl6_6
    | ~ spl6_64 ),
    inference(resolution,[],[f716,f132])).

fof(f716,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f715])).

fof(f728,plain,
    ( spl6_65
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f583,f547,f170,f160,f115,f110,f105,f726])).

fof(f547,plain,
    ( spl6_52
  <=> ! [X1,X3,X0,X2] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f583,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f582,f107])).

fof(f582,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f581,f112])).

fof(f581,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f580,f117])).

fof(f580,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f579,f162])).

fof(f579,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_14
    | ~ spl6_52 ),
    inference(resolution,[],[f548,f172])).

fof(f548,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f547])).

fof(f717,plain,
    ( spl6_64
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f574,f540,f170,f160,f115,f110,f105,f715])).

fof(f540,plain,
    ( spl6_51
  <=> ! [X1,X3,X0,X2] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f574,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f573,f107])).

fof(f573,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f572,f112])).

fof(f572,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f571,f117])).

fof(f571,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f570,f162])).

fof(f570,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(resolution,[],[f541,f172])).

fof(f541,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f540])).

fof(f549,plain,
    ( spl6_52
    | spl6_7
    | spl6_8
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f364,f175,f140,f135,f547])).

fof(f175,plain,
    ( spl6_15
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f364,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_7
    | spl6_8
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f363,f137])).

fof(f363,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_8
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f362,f142])).

fof(f362,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_15 ),
    inference(resolution,[],[f359,f177])).

fof(f177,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f359,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f358,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f358,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f357,f89])).

fof(f357,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f93,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | r1_tsep_1(X2,X3) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_tmap_1)).

fof(f542,plain,
    ( spl6_51
    | spl6_7
    | spl6_8
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f352,f175,f140,f135,f540])).

fof(f352,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_7
    | spl6_8
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f351,f137])).

fof(f351,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_8
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f350,f142])).

fof(f350,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_15 ),
    inference(resolution,[],[f337,f177])).

fof(f337,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f336,f88])).

fof(f336,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f335,f89])).

fof(f335,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f91,f87])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f538,plain,
    ( spl6_50
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f518,f508,f170,f535])).

fof(f508,plain,
    ( spl6_48
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f518,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(resolution,[],[f509,f172])).

fof(f509,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f508])).

fof(f532,plain,
    ( spl6_49
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f517,f508,f160,f529])).

fof(f517,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(resolution,[],[f509,f162])).

fof(f510,plain,
    ( spl6_48
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f502,f487,f170,f160,f140,f135,f115,f110,f105,f508])).

fof(f487,plain,
    ( spl6_45
  <=> ! [X1,X0] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f501,f137])).

fof(f501,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f500,f162])).

fof(f500,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_8
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f499,f142])).

fof(f499,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f498,f172])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f497,f107])).

fof(f497,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f496,f112])).

fof(f496,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl6_3
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f495,f117])).

fof(f495,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl6_45 ),
    inference(duplicate_literal_removal,[],[f494])).

fof(f494,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_45 ),
    inference(resolution,[],[f488,f81])).

fof(f488,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f487])).

fof(f489,plain,
    ( spl6_45
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f485,f460,f250,f205,f200,f195,f190,f170,f160,f150,f145,f140,f135,f130,f125,f120,f115,f110,f105,f487])).

fof(f460,plain,
    ( spl6_43
  <=> ! [X5,X7,X8,X6] :
        ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X5),u1_struct_0(X6))
        | v1_funct_1(k3_tmap_1(X7,X6,X5,X8,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(X5,X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f485,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f484,f107])).

fof(f484,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f483,f112])).

fof(f483,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f482,f117])).

fof(f482,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f481,f137])).

fof(f481,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f480,f162])).

fof(f480,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f479,f142])).

fof(f479,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f478,f172])).

fof(f478,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f477,f147])).

fof(f477,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f476,f192])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f475,f202])).

fof(f475,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f474,f152])).

fof(f474,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f473,f197])).

fof(f473,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f472,f207])).

fof(f472,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f471,f122])).

fof(f471,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f470,f127])).

fof(f470,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_6
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f469,f132])).

fof(f469,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_28
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f468,f251])).

fof(f468,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_43 ),
    inference(duplicate_literal_removal,[],[f467])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_43 ),
    inference(resolution,[],[f461,f89])).

fof(f461,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X5),u1_struct_0(X6))
        | v1_funct_1(k3_tmap_1(X7,X6,X5,X8,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(X5,X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f460])).

fof(f462,plain,
    ( spl6_43
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f267,f246,f460])).

fof(f267,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X5),u1_struct_0(X6))
        | v1_funct_1(k3_tmap_1(X7,X6,X5,X8,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(X5,X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl6_27 ),
    inference(resolution,[],[f247,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f297,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f295,f107])).

fof(f295,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f294,f112])).

fof(f294,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f293,f117])).

fof(f293,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f292,f122])).

fof(f292,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f291,f127])).

fof(f291,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f290,f132])).

fof(f290,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f289,f137])).

fof(f289,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f288,f162])).

fof(f288,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f287,f142])).

fof(f287,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f286,f172])).

fof(f286,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f285,f147])).

fof(f285,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f284,f192])).

fof(f284,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f283,f202])).

fof(f283,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f282,f152])).

fof(f282,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_19
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f281,f197])).

fof(f281,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_21
    | spl6_28 ),
    inference(subsumption_resolution,[],[f279,f207])).

fof(f279,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_28 ),
    inference(resolution,[],[f88,f252])).

fof(f252,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f265,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | spl6_27 ),
    inference(unit_resulting_resolution,[],[f107,f112,f117,f122,f127,f132,f137,f147,f142,f152,f162,f172,f192,f248,f202,f197,f207,f87])).

fof(f248,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f246])).

fof(f261,plain,
    ( ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f58,f258,f254,f250,f246])).

fof(f58,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(sK5,sK3,sK1)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK3,sK0)
    & v1_borsuk_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & v1_borsuk_1(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f29,f28,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & r1_tsep_1(X2,X3)
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,sK0)
                  & v1_borsuk_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & v1_borsuk_1(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),X1)
                          | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & r1_tsep_1(X2,X3)
                & m1_pre_topc(X3,sK0)
                & v1_borsuk_1(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & v1_borsuk_1(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))))
                        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),sK1)
                        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))
                        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(X5,X3,sK1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                  & v5_pre_topc(X4,X2,sK1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,sK0)
              & v1_borsuk_1(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & v1_borsuk_1(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))))
                      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),sK1)
                      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))
                      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(X5,X3,sK1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v5_pre_topc(X4,X2,sK1)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & r1_tsep_1(X2,X3)
            & m1_pre_topc(X3,sK0)
            & v1_borsuk_1(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & v1_borsuk_1(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_tsep_1(sK0,sK2,X3),sK1)
                    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))
                    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(X5,X3,sK1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(X4,sK2,sK1)
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & r1_tsep_1(sK2,X3)
          & m1_pre_topc(X3,sK0)
          & v1_borsuk_1(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & v1_borsuk_1(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_tsep_1(sK0,sK2,X3),sK1)
                  | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))
                  | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(X5,X3,sK1)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(X4,sK2,sK1)
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & r1_tsep_1(sK2,X3)
        & m1_pre_topc(X3,sK0)
        & v1_borsuk_1(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
                | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
                | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(X5,sK3,sK1)
              & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(X4,sK2,sK1)
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & r1_tsep_1(sK2,sK3)
      & m1_pre_topc(sK3,sK0)
      & v1_borsuk_1(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
              | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
              | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v5_pre_topc(X5,sK3,sK1)
            & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v5_pre_topc(X4,sK2,sK1)
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
            | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
            | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(X5,sK3,sK1)
          & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(sK4,sK2,sK1)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
          | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
          | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(X5,sK3,sK1)
        & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v5_pre_topc(sK5,sK3,sK1)
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( r1_tsep_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(X4,X2,X1)
                            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v5_pre_topc(X5,X3,X1)
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_tmap_1)).

fof(f208,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f57,f205])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f203,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f53,f200])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f198,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f55,f195])).

fof(f55,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f193,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f51,f190])).

fof(f51,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f188,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f56,f185])).

fof(f185,plain,
    ( spl6_17
  <=> v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f56,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f183,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f52,f180])).

fof(f52,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f178,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f49,f175])).

fof(f49,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f173,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f48,f170])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f168,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f47,f165])).

fof(f47,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f163,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f45,f160])).

fof(f45,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f158,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f44,f155])).

fof(f44,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f153,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f54,f150])).

fof(f54,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f148,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f50,f145])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f143,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f46,f140])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f138,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f43,f135])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f133,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f42,f130])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f128,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f41,f125])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f123,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f40,f120])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f118,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f39,f115])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f113,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f38,f110])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f108,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f105])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
