%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t120_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:05 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  329 ( 662 expanded)
%              Number of leaves         :   69 ( 244 expanded)
%              Depth                    :   25
%              Number of atoms          : 1557 (2865 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f998,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f149,f156,f163,f170,f177,f184,f191,f198,f213,f225,f245,f253,f278,f299,f309,f337,f446,f449,f455,f462,f469,f475,f492,f515,f537,f543,f561,f571,f575,f594,f600,f604,f651,f658,f734,f751,f906,f953,f997])).

fof(f997,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_66 ),
    inference(avatar_contradiction_clause,[],[f996])).

fof(f996,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f995,f155])).

fof(f155,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl8_5
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f995,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f994,f190])).

fof(f190,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl8_14
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f994,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f993,f169])).

fof(f169,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl8_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f993,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f992,f162])).

fof(f162,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl8_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f992,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_66 ),
    inference(resolution,[],[f587,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',fc5_tmap_1)).

fof(f587,plain,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl8_66
  <=> v2_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f953,plain,
    ( spl8_1
    | spl8_3
    | spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_26
    | spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_64 ),
    inference(avatar_contradiction_clause,[],[f952])).

fof(f952,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_64 ),
    inference(subsumption_resolution,[],[f951,f155])).

fof(f951,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_64 ),
    inference(subsumption_resolution,[],[f950,f581])).

fof(f581,plain,
    ( m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl8_64
  <=> m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f950,plain,
    ( ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f949,f183])).

fof(f183,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl8_12
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f949,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f948,f176])).

fof(f176,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl8_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f948,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f947,f190])).

fof(f947,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f946,f148])).

fof(f148,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_3
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f946,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f945,f169])).

fof(f945,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f944,f162])).

fof(f944,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f943,f265])).

fof(f265,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_29
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f943,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_26
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f942,f141])).

fof(f141,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f942,plain,
    ( v2_struct_0(sK2)
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_26
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f941,f268])).

fof(f268,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl8_30
  <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f941,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK2)
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f935,f274])).

fof(f274,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl8_32
  <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f935,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK2)
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl8_26 ),
    inference(resolution,[],[f371,f256])).

fof(f256,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl8_26
  <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f371,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))
      | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_subset_1(sK4(k8_tmap_1(X0,X1),X2,k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f370,f127])).

fof(f370,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X2)
      | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))
      | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
      | v2_struct_0(k8_tmap_1(X0,X1))
      | v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_subset_1(sK4(k8_tmap_1(X0,X1),X2,k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f369,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',dt_k8_tmap_1)).

fof(f369,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X2)
      | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))
      | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
      | v2_struct_0(k8_tmap_1(X0,X1))
      | v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_subset_1(sK4(k8_tmap_1(X0,X1),X2,k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f368,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f368,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X2)
      | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))
      | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
      | v2_struct_0(k8_tmap_1(X0,X1))
      | v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_subset_1(sK4(k8_tmap_1(X0,X1),X2,k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f367,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',dt_m1_pre_topc)).

fof(f367,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))
      | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
      | v2_struct_0(k8_tmap_1(X0,X1))
      | v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_subset_1(sK4(k8_tmap_1(X0,X1),X2,k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f366,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',cc1_pre_topc)).

fof(f366,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))
      | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
      | v2_struct_0(k8_tmap_1(X0,X1))
      | v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_subset_1(sK4(k8_tmap_1(X0,X1),X2,k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))
      | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
      | v2_struct_0(k8_tmap_1(X0,X1))
      | v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_subset_1(sK4(k8_tmap_1(X0,X1),X2,k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f113,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
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
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',t118_tmap_1)).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',t49_tmap_1)).

fof(f906,plain,
    ( spl8_80
    | ~ spl8_50
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f872,f656,f464,f904])).

fof(f904,plain,
    ( spl8_80
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f464,plain,
    ( spl8_50
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f656,plain,
    ( spl8_74
  <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f872,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_50
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f866,f465])).

fof(f465,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f464])).

fof(f866,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_74 ),
    inference(superposition,[],[f217,f657])).

fof(f657,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f656])).

fof(f217,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f123,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',dt_g1_pre_topc)).

fof(f123,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',dt_u1_pre_topc)).

fof(f751,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | spl8_77 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_77 ),
    inference(subsumption_resolution,[],[f749,f155])).

fof(f749,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_77 ),
    inference(subsumption_resolution,[],[f748,f176])).

fof(f748,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_77 ),
    inference(subsumption_resolution,[],[f747,f169])).

fof(f747,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_77 ),
    inference(subsumption_resolution,[],[f746,f162])).

fof(f746,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_77 ),
    inference(resolution,[],[f727,f126])).

fof(f727,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK2))
    | ~ spl8_77 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl8_77
  <=> ~ l1_pre_topc(k8_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f734,plain,
    ( ~ spl8_77
    | spl8_78
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f704,f649,f732,f726])).

fof(f732,plain,
    ( spl8_78
  <=> v1_pre_topc(k8_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f649,plain,
    ( spl8_72
  <=> k8_tmap_1(sK0,sK2) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK2)),u1_pre_topc(k8_tmap_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f704,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK2))
    | ~ spl8_72 ),
    inference(superposition,[],[f217,f650])).

fof(f650,plain,
    ( k8_tmap_1(sK0,sK2) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK2)),u1_pre_topc(k8_tmap_1(sK0,sK2)))
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f649])).

fof(f658,plain,
    ( spl8_74
    | spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f644,f189,f168,f161,f154,f656])).

fof(f644,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f643,f155])).

fof(f643,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f642,f162])).

fof(f642,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f636,f169])).

fof(f636,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_14 ),
    inference(resolution,[],[f238,f190])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f237,f126])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) ) ),
    inference(resolution,[],[f124,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',abstractness_v1_pre_topc)).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f651,plain,
    ( spl8_72
    | spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f641,f175,f168,f161,f154,f649])).

fof(f641,plain,
    ( k8_tmap_1(sK0,sK2) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK2)),u1_pre_topc(k8_tmap_1(sK0,sK2)))
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f640,f155])).

fof(f640,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK2) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK2)),u1_pre_topc(k8_tmap_1(sK0,sK2)))
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f639,f162])).

fof(f639,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK2) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK2)),u1_pre_topc(k8_tmap_1(sK0,sK2)))
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f635,f169])).

fof(f635,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK2) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK2)),u1_pre_topc(k8_tmap_1(sK0,sK2)))
    | ~ spl8_10 ),
    inference(resolution,[],[f238,f176])).

fof(f604,plain,
    ( spl8_70
    | ~ spl8_33
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f524,f255,f276,f602])).

fof(f602,plain,
    ( spl8_70
  <=> ! [X3] : k2_partfun1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3) = k7_relat_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f276,plain,
    ( spl8_33
  <=> ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f524,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3) = k7_relat_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3) )
    | ~ spl8_26 ),
    inference(resolution,[],[f256,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',redefinition_k2_partfun1)).

fof(f600,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | spl8_69 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_69 ),
    inference(subsumption_resolution,[],[f598,f155])).

fof(f598,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_69 ),
    inference(subsumption_resolution,[],[f597,f190])).

fof(f597,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_69 ),
    inference(subsumption_resolution,[],[f596,f169])).

fof(f596,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_69 ),
    inference(subsumption_resolution,[],[f595,f162])).

fof(f595,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_69 ),
    inference(resolution,[],[f593,f125])).

fof(f593,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_69 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl8_69
  <=> ~ v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f594,plain,
    ( spl8_64
    | spl8_66
    | ~ spl8_33
    | ~ spl8_69
    | spl8_1
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_26
    | spl8_29
    | ~ spl8_30
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f552,f464,f267,f264,f255,f243,f211,f140,f592,f276,f586,f580])).

fof(f211,plain,
    ( spl8_18
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f243,plain,
    ( spl8_22
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f552,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f551,f265])).

fof(f551,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_30
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f550,f268])).

fof(f550,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f549,f212])).

fof(f212,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f549,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f548,f244])).

fof(f244,plain,
    ( v2_pre_topc(sK2)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f243])).

fof(f548,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_26
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f547,f141])).

fof(f547,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_26
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f522,f465])).

fof(f522,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK4(k8_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)),u1_struct_0(sK2))
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_26 ),
    inference(resolution,[],[f256,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f575,plain,
    ( spl8_62
    | ~ spl8_33
    | ~ spl8_26
    | ~ spl8_30
    | ~ spl8_38
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f546,f441,f294,f267,f255,f276,f573])).

fof(f573,plain,
    ( spl8_62
  <=> ! [X2] :
        ( ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f294,plain,
    ( spl8_38
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f441,plain,
    ( spl8_48
  <=> l1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f546,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X2)) )
    | ~ spl8_26
    | ~ spl8_30
    | ~ spl8_38
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f545,f295])).

fof(f295,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f294])).

fof(f545,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X2)) )
    | ~ spl8_26
    | ~ spl8_30
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f544,f268])).

fof(f544,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
        | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X2)) )
    | ~ spl8_26
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f523,f442])).

fof(f442,plain,
    ( l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f441])).

fof(f523,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
        | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X2)) )
    | ~ spl8_26 ),
    inference(resolution,[],[f256,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',dt_k2_tmap_1)).

fof(f571,plain,
    ( ~ spl8_59
    | spl8_60
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f483,f423,f569,f566])).

fof(f566,plain,
    ( spl8_59
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f569,plain,
    ( spl8_60
  <=> ! [X6] : ~ r2_hidden(X6,k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f423,plain,
    ( spl8_42
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f483,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k9_tmap_1(sK0,sK1))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))) )
    | ~ spl8_42 ),
    inference(resolution,[],[f424,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',t5_subset)).

fof(f424,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f423])).

fof(f561,plain,
    ( spl8_56
    | ~ spl8_33
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f525,f255,f276,f559])).

fof(f559,plain,
    ( spl8_56
  <=> ! [X4] : v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f525,plain,
    ( ! [X4] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
        | v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X4)) )
    | ~ spl8_26 ),
    inference(resolution,[],[f256,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',dt_k2_partfun1)).

fof(f543,plain,
    ( spl8_33
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46
    | ~ spl8_48 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl8_33
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f541,f295])).

fof(f541,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl8_33
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46
    | ~ spl8_48 ),
    inference(resolution,[],[f519,f277])).

fof(f277,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f276])).

fof(f519,plain,
    ( ! [X2] :
        ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2))
        | ~ l1_struct_0(X2) )
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f518,f418])).

fof(f418,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl8_40
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f518,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2)) )
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f517,f430])).

fof(f430,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl8_44
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f517,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2)) )
    | ~ spl8_42
    | ~ spl8_46
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f516,f436])).

fof(f436,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl8_46
  <=> v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f516,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2)) )
    | ~ spl8_42
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f479,f442])).

fof(f479,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
        | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2)) )
    | ~ spl8_42 ),
    inference(resolution,[],[f424,f92])).

fof(f537,plain,
    ( ~ spl8_53
    | spl8_54
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f527,f255,f535,f532])).

fof(f532,plain,
    ( spl8_53
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f535,plain,
    ( spl8_54
  <=> ! [X6] : ~ r2_hidden(X6,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f527,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))) )
    | ~ spl8_26 ),
    inference(resolution,[],[f256,f95])).

fof(f515,plain,
    ( spl8_27
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46
    | ~ spl8_48 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl8_27
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f442,f497])).

fof(f497,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl8_27
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f496,f418])).

fof(f496,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl8_27
    | ~ spl8_38
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f495,f295])).

fof(f495,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ spl8_27
    | ~ spl8_42
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f494,f424])).

fof(f494,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ spl8_27
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f493,f430])).

fof(f493,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ spl8_27
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f338,f436])).

fof(f338,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ spl8_27 ),
    inference(resolution,[],[f94,f259])).

fof(f259,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl8_27
  <=> ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f492,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | spl8_51 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f490,f155])).

fof(f490,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f489,f190])).

fof(f489,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f488,f169])).

fof(f488,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f487,f162])).

fof(f487,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_51 ),
    inference(resolution,[],[f468,f126])).

fof(f468,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl8_51
  <=> ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f475,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | spl8_43 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f473,f155])).

fof(f473,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f472,f190])).

fof(f472,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f471,f169])).

fof(f471,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f470,f162])).

fof(f470,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_43 ),
    inference(resolution,[],[f427,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',dt_k9_tmap_1)).

fof(f427,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl8_43
  <=> ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f469,plain,
    ( ~ spl8_51
    | spl8_49 ),
    inference(avatar_split_clause,[],[f456,f444,f467])).

fof(f444,plain,
    ( spl8_49
  <=> ~ l1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f456,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_49 ),
    inference(resolution,[],[f445,f135])).

fof(f135,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',dt_l1_pre_topc)).

fof(f445,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f444])).

fof(f462,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | spl8_45 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f460,f155])).

fof(f460,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f459,f190])).

fof(f459,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f458,f169])).

fof(f458,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f457,f162])).

fof(f457,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_45 ),
    inference(resolution,[],[f433,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f433,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl8_45
  <=> ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f455,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | spl8_47 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f453,f155])).

fof(f453,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f452,f190])).

fof(f452,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f451,f169])).

fof(f451,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f450,f162])).

fof(f450,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_47 ),
    inference(resolution,[],[f439,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f439,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl8_47
  <=> ~ v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f449,plain,
    ( ~ spl8_8
    | spl8_41 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f447,f169])).

fof(f447,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_41 ),
    inference(resolution,[],[f421,f135])).

fof(f421,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl8_41
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f446,plain,
    ( ~ spl8_41
    | ~ spl8_39
    | ~ spl8_43
    | ~ spl8_45
    | ~ spl8_47
    | ~ spl8_49
    | spl8_31 ),
    inference(avatar_split_clause,[],[f334,f270,f444,f438,f432,f426,f297,f420])).

fof(f297,plain,
    ( spl8_39
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f270,plain,
    ( spl8_31
  <=> ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f334,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ spl8_31 ),
    inference(resolution,[],[f93,f271])).

fof(f271,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f270])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f337,plain,
    ( ~ spl8_18
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl8_18
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f335,f212])).

fof(f335,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl8_39 ),
    inference(resolution,[],[f298,f135])).

fof(f298,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f297])).

fof(f309,plain,
    ( ~ spl8_20
    | spl8_37 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | ~ spl8_20
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f307,f224])).

fof(f224,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl8_20
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f307,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_37 ),
    inference(resolution,[],[f292,f135])).

fof(f292,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl8_37
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f299,plain,
    ( spl8_34
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f236,f182,f297,f291,f285])).

fof(f285,plain,
    ( spl8_34
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f236,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK2,sK1)
    | ~ spl8_12 ),
    inference(resolution,[],[f130,f183])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',symmetry_r1_tsep_1)).

fof(f278,plain,
    ( ~ spl8_27
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f83,f276,f270,f264,f258])).

fof(f83,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
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
               => ( r1_tsep_1(X1,X2)
                 => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
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
             => ( r1_tsep_1(X1,X2)
               => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',t120_tmap_1)).

fof(f253,plain,
    ( spl8_24
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f233,f189,f168,f161,f251])).

fof(f251,plain,
    ( spl8_24
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f233,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f232,f162])).

fof(f232,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1)
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f227,f169])).

fof(f227,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1)
    | ~ spl8_14 ),
    inference(resolution,[],[f131,f190])).

fof(f245,plain,
    ( spl8_22
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f231,f175,f168,f161,f243])).

fof(f231,plain,
    ( v2_pre_topc(sK2)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f230,f162])).

fof(f230,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f226,f169])).

fof(f226,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f131,f176])).

fof(f225,plain,
    ( spl8_20
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f204,f189,f168,f223])).

fof(f204,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f200,f169])).

fof(f200,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl8_14 ),
    inference(resolution,[],[f133,f190])).

fof(f213,plain,
    ( spl8_18
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f203,f175,f168,f211])).

fof(f203,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f199,f169])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f133,f176])).

fof(f198,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f134,f196])).

fof(f196,plain,
    ( spl8_16
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f134,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t120_tmap_1.p',existence_l1_pre_topc)).

fof(f191,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f88,f189])).

fof(f88,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f184,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f86,f182])).

fof(f86,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f177,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f85,f175])).

fof(f85,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f170,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f91,f168])).

fof(f91,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f163,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f90,f161])).

fof(f90,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f156,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f89,f154])).

fof(f89,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f149,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f87,f147])).

fof(f87,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f142,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f84,f140])).

fof(f84,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
