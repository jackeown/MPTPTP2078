%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t70_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:56 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 410 expanded)
%              Number of leaves         :   46 ( 169 expanded)
%              Depth                    :   13
%              Number of atoms          :  740 (1524 expanded)
%              Number of equality atoms :   76 ( 110 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f550,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f123,f127,f131,f135,f143,f147,f169,f173,f177,f184,f196,f200,f241,f257,f261,f272,f276,f280,f296,f300,f341,f367,f425,f444,f463,f475,f547,f548,f549])).

fof(f549,plain,
    ( k1_xboole_0 != sK3(sK0,sK1,sK2)
    | k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    | v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(theory_axiom,[])).

fof(f548,plain,
    ( u1_struct_0(sK1) != sK3(sK0,sK1,sK2)
    | u1_struct_0(sK0) != k10_relat_1(sK2,u1_struct_0(sK1))
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(theory_axiom,[])).

fof(f547,plain,
    ( spl8_102
    | spl8_104
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_46
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f308,f294,f270,f133,f129,f125,f545,f542])).

fof(f542,plain,
    ( spl8_102
  <=> u1_struct_0(sK1) = sK3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f545,plain,
    ( spl8_104
  <=> k1_xboole_0 = sK3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f125,plain,
    ( spl8_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f129,plain,
    ( spl8_6
  <=> v2_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f133,plain,
    ( spl8_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f270,plain,
    ( spl8_46
  <=> v4_pre_topc(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f294,plain,
    ( spl8_52
  <=> m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f308,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,sK2)
    | u1_struct_0(sK1) = sK3(sK0,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_46
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f307,f130])).

fof(f130,plain,
    ( v2_tdlat_3(sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f307,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,sK2)
    | u1_struct_0(sK1) = sK3(sK0,sK1,sK2)
    | ~ v2_tdlat_3(sK1)
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_46
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f306,f271])).

fof(f271,plain,
    ( v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f270])).

fof(f306,plain,
    ( ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | k1_xboole_0 = sK3(sK0,sK1,sK2)
    | u1_struct_0(sK1) = sK3(sK0,sK1,sK2)
    | ~ v2_tdlat_3(sK1)
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f305,f126])).

fof(f126,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f305,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | k1_xboole_0 = sK3(sK0,sK1,sK2)
    | u1_struct_0(sK1) = sK3(sK0,sK1,sK2)
    | ~ v2_tdlat_3(sK1)
    | ~ spl8_8
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f301,f134])).

fof(f134,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f301,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | k1_xboole_0 = sK3(sK0,sK1,sK2)
    | u1_struct_0(sK1) = sK3(sK0,sK1,sK2)
    | ~ v2_tdlat_3(sK1)
    | ~ spl8_52 ),
    inference(resolution,[],[f295,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k1_xboole_0 = X1
      | u1_struct_0(X0) = X1
      | ~ v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( u1_struct_0(X0) != X1
                & k1_xboole_0 != X1
                & v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',t21_tdlat_3)).

fof(f295,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f294])).

fof(f475,plain,
    ( ~ spl8_87
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | spl8_19
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f315,f194,f182,f171,f145,f133,f117,f473])).

fof(f473,plain,
    ( spl8_87
  <=> ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f117,plain,
    ( spl8_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f145,plain,
    ( spl8_14
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f171,plain,
    ( spl8_19
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f182,plain,
    ( spl8_22
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f194,plain,
    ( spl8_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f315,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f314,f172])).

fof(f172,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f314,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f313,f146])).

fof(f146,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f313,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f312,f195])).

fof(f195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f194])).

fof(f312,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f311,f183])).

fof(f183,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f311,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f310,f118])).

fof(f118,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f117])).

fof(f310,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f309,f134])).

fof(f309,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_26 ),
    inference(superposition,[],[f85,f207])).

fof(f207,plain,
    ( ! [X1] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1)
    | ~ spl8_26 ),
    inference(resolution,[],[f195,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',redefinition_k8_relset_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',d12_pre_topc)).

fof(f463,plain,
    ( spl8_80
    | ~ spl8_26
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f415,f339,f194,f461])).

fof(f461,plain,
    ( spl8_80
  <=> u1_struct_0(sK0) = k10_relat_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f339,plain,
    ( spl8_64
  <=> u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f415,plain,
    ( u1_struct_0(sK0) = k10_relat_1(sK2,u1_struct_0(sK1))
    | ~ spl8_26
    | ~ spl8_64 ),
    inference(superposition,[],[f340,f207])).

fof(f340,plain,
    ( u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f339])).

fof(f444,plain,
    ( spl8_74
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_70 ),
    inference(avatar_split_clause,[],[f436,f423,f145,f141,f442])).

fof(f442,plain,
    ( spl8_74
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f141,plain,
    ( spl8_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f423,plain,
    ( spl8_70
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f436,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f435,f108])).

fof(f108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',fc1_xboole_0)).

fof(f435,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f434,f142])).

fof(f142,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f434,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_14
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f431,f146])).

fof(f431,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_70 ),
    inference(resolution,[],[f424,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',cc2_pre_topc)).

fof(f424,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f423])).

fof(f425,plain,
    ( spl8_70
    | ~ spl8_26
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f417,f278,f194,f423])).

fof(f278,plain,
    ( spl8_50
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f417,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_26
    | ~ spl8_50 ),
    inference(superposition,[],[f236,f279])).

fof(f279,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f278])).

fof(f236,plain,
    ( ! [X2] : m1_subset_1(k10_relat_1(sK2,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f208,f207])).

fof(f208,plain,
    ( ! [X2] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_26 ),
    inference(resolution,[],[f195,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',dt_k8_relset_1)).

fof(f367,plain,
    ( spl8_55
    | ~ spl8_62 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl8_55
    | ~ spl8_62 ),
    inference(subsumption_resolution,[],[f350,f108])).

fof(f350,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_55
    | ~ spl8_62 ),
    inference(superposition,[],[f299,f337])).

fof(f337,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl8_62
  <=> u1_struct_0(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f299,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl8_55
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f341,plain,
    ( spl8_62
    | spl8_64
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f217,f194,f182,f175,f167,f117,f339,f336])).

fof(f167,plain,
    ( spl8_16
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f175,plain,
    ( spl8_20
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f217,plain,
    ( u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | u1_struct_0(sK1) = k1_xboole_0
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f216,f178])).

fof(f178,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl8_16 ),
    inference(resolution,[],[f168,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',d3_struct_0)).

fof(f168,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f216,plain,
    ( u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | u1_struct_0(sK1) = k1_xboole_0
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f215,f185])).

fof(f185,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_20 ),
    inference(resolution,[],[f176,f93])).

fof(f176,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f215,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f214,f178])).

fof(f214,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f213,f176])).

fof(f213,plain,
    ( ~ l1_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f212,f183])).

fof(f212,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f211,f118])).

fof(f211,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f202,f168])).

fof(f202,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | ~ spl8_26 ),
    inference(resolution,[],[f195,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | k2_struct_0(X1) = k1_xboole_0
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',t52_tops_2)).

fof(f300,plain,
    ( ~ spl8_55
    | spl8_3
    | ~ spl8_16
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f292,f259,f167,f121,f298])).

fof(f121,plain,
    ( spl8_3
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f259,plain,
    ( spl8_40
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f292,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f291,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f291,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl8_16
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f290,f168])).

fof(f290,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_40 ),
    inference(superposition,[],[f102,f260])).

fof(f260,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f259])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',fc5_struct_0)).

fof(f296,plain,
    ( spl8_52
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | spl8_19
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f230,f194,f182,f171,f145,f133,f117,f294])).

fof(f230,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f229,f172])).

fof(f229,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f228,f146])).

fof(f228,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f227,f183])).

fof(f227,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f226,f118])).

fof(f226,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f205,f134])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_26 ),
    inference(resolution,[],[f195,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f280,plain,
    ( spl8_50
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f249,f239,f278])).

fof(f239,plain,
    ( spl8_30
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f249,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl8_30 ),
    inference(resolution,[],[f240,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',t171_relat_1)).

fof(f240,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f239])).

fof(f276,plain,
    ( spl8_48
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f185,f175,f274])).

fof(f274,plain,
    ( spl8_48
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f272,plain,
    ( spl8_46
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | spl8_19
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f235,f194,f182,f171,f145,f133,f117,f270])).

fof(f235,plain,
    ( v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f234,f172])).

fof(f234,plain,
    ( v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f233,f146])).

fof(f233,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f232,f183])).

fof(f232,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f231,f118])).

fof(f231,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f206,f134])).

fof(f206,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_26 ),
    inference(resolution,[],[f195,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(sK3(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f261,plain,
    ( spl8_40
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f178,f167,f259])).

fof(f257,plain,
    ( spl8_38
    | ~ spl8_20
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f201,f198,f175,f255])).

fof(f255,plain,
    ( spl8_38
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f198,plain,
    ( spl8_28
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f201,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl8_20
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f199,f185])).

fof(f199,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f198])).

fof(f241,plain,
    ( spl8_30
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f237,f194,f239])).

fof(f237,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f209,f88])).

fof(f88,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',fc6_relat_1)).

fof(f209,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2)
    | ~ spl8_26 ),
    inference(resolution,[],[f195,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',cc2_relat_1)).

fof(f200,plain,
    ( spl8_28
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f161,f145,f141,f198])).

fof(f161,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f156,f142])).

fof(f156,plain,
    ( ~ v2_pre_topc(sK0)
    | v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f146,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',fc4_pre_topc)).

fof(f196,plain,(
    spl8_26 ),
    inference(avatar_split_clause,[],[f73,f194])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_tdlat_3(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_tdlat_3(X1)
          & v2_pre_topc(X1)
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
            ( ( l1_pre_topc(X1)
              & v2_tdlat_3(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_tdlat_3(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',t70_tex_2)).

fof(f184,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f72,f182])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f177,plain,
    ( spl8_20
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f155,f145,f175])).

fof(f155,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f146,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t70_tex_2.p',dt_l1_pre_topc)).

fof(f173,plain,(
    ~ spl8_19 ),
    inference(avatar_split_clause,[],[f74,f171])).

fof(f74,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f169,plain,
    ( spl8_16
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f148,f133,f167])).

fof(f148,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_8 ),
    inference(resolution,[],[f134,f101])).

fof(f147,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f81,f145])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f143,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f80,f141])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f135,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f78,f133])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f131,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f77,f129])).

fof(f77,plain,(
    v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f127,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f76,f125])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f123,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f75,f121])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f119,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f71,f117])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
