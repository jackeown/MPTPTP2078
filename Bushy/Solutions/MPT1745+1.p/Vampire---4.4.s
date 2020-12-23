%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t54_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:16 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 473 expanded)
%              Number of leaves         :   45 ( 193 expanded)
%              Depth                    :   25
%              Number of atoms          : 1411 (3251 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f442,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f108,f115,f122,f129,f136,f143,f150,f157,f164,f171,f178,f185,f192,f199,f206,f213,f220,f227,f234,f253,f307,f362,f380,f387,f391,f417,f424,f428,f438,f441])).

fof(f441,plain,
    ( ~ spl9_8
    | spl9_61 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_61 ),
    inference(subsumption_resolution,[],[f439,f128])).

fof(f128,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl9_8
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f439,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl9_61 ),
    inference(resolution,[],[f423,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',dt_l1_pre_topc)).

fof(f423,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl9_61
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f438,plain,
    ( spl9_64
    | spl9_66
    | ~ spl9_0
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f273,f211,f197,f99,f436,f433])).

fof(f433,plain,
    ( spl9_64
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f436,plain,
    ( spl9_66
  <=> ! [X18,X17] :
        ( ~ v1_funct_1(X17)
        | v1_funct_1(k5_relat_1(X17,sK4))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X18,u1_struct_0(sK0))))
        | ~ v1_funct_2(X17,X18,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f99,plain,
    ( spl9_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f197,plain,
    ( spl9_28
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f211,plain,
    ( spl9_32
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f273,plain,
    ( ! [X17,X18] :
        ( ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X18,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X18,u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_funct_1(k5_relat_1(X17,sK4)) )
    | ~ spl9_0
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f272,f198])).

fof(f198,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f197])).

fof(f272,plain,
    ( ! [X17,X18] :
        ( ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X18,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X18,u1_struct_0(sK0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_funct_1(k5_relat_1(X17,sK4)) )
    | ~ spl9_0
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f267,f100])).

fof(f100,plain,
    ( v1_funct_1(sK4)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f99])).

fof(f267,plain,
    ( ! [X17,X18] :
        ( ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X18,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X18,u1_struct_0(sK0))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_funct_1(k5_relat_1(X17,sK4)) )
    | ~ spl9_32 ),
    inference(resolution,[],[f83,f212])).

fof(f212,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f211])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | v1_xboole_0(X1)
      | v1_funct_1(k5_relat_1(X3,X4)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X4,X1,X2)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X1) )
     => ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',fc8_funct_2)).

fof(f428,plain,
    ( spl9_54
    | spl9_62
    | ~ spl9_2
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f271,f218,f204,f106,f426,f385])).

fof(f385,plain,
    ( spl9_54
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f426,plain,
    ( spl9_62
  <=> ! [X16,X15] :
        ( ~ v1_funct_1(X15)
        | v1_funct_1(k5_relat_1(X15,sK3))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,u1_struct_0(sK2))))
        | ~ v1_funct_2(X15,X16,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f106,plain,
    ( spl9_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f204,plain,
    ( spl9_30
  <=> v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f218,plain,
    ( spl9_34
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f271,plain,
    ( ! [X15,X16] :
        ( ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X16,u1_struct_0(sK2))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,u1_struct_0(sK2))))
        | v1_xboole_0(u1_struct_0(sK2))
        | v1_funct_1(k5_relat_1(X15,sK3)) )
    | ~ spl9_2
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f270,f205])).

fof(f205,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f204])).

fof(f270,plain,
    ( ! [X15,X16] :
        ( ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X16,u1_struct_0(sK2))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,u1_struct_0(sK2))))
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK2))
        | v1_funct_1(k5_relat_1(X15,sK3)) )
    | ~ spl9_2
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f266,f107])).

fof(f107,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f266,plain,
    ( ! [X15,X16] :
        ( ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X16,u1_struct_0(sK2))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,u1_struct_0(sK2))))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK2))
        | v1_funct_1(k5_relat_1(X15,sK3)) )
    | ~ spl9_34 ),
    inference(resolution,[],[f83,f219])).

fof(f219,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f218])).

fof(f424,plain,
    ( ~ spl9_61
    | spl9_5
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f393,f385,f113,f422])).

fof(f113,plain,
    ( spl9_5
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f393,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl9_5
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f392,f114])).

fof(f114,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f392,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_54 ),
    inference(resolution,[],[f386,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',fc2_struct_0)).

fof(f386,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f385])).

fof(f417,plain,
    ( ~ spl9_59
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_32
    | ~ spl9_34
    | spl9_39 ),
    inference(avatar_split_clause,[],[f409,f232,f218,f211,f106,f99,f415])).

fof(f415,plain,
    ( spl9_59
  <=> ~ r1_tmap_1(sK2,sK1,k5_relat_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f232,plain,
    ( spl9_39
  <=> ~ r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f409,plain,
    ( ~ r1_tmap_1(sK2,sK1,k5_relat_1(sK3,sK4),sK5)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(backward_demodulation,[],[f408,f233])).

fof(f233,plain,
    ( ~ r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f232])).

fof(f408,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f404,f107])).

fof(f404,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl9_0
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(resolution,[],[f259,f219])).

fof(f259,plain,
    ( ! [X12,X13,X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ v1_funct_1(X11)
        | k1_partfun1(X12,X13,u1_struct_0(sK0),u1_struct_0(sK1),X11,sK4) = k5_relat_1(X11,sK4) )
    | ~ spl9_0
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f256,f100])).

fof(f256,plain,
    ( ! [X12,X13,X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(X11)
        | k1_partfun1(X12,X13,u1_struct_0(sK0),u1_struct_0(sK1),X11,sK4) = k5_relat_1(X11,sK4) )
    | ~ spl9_32 ),
    inference(resolution,[],[f78,f212])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_1(X4)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',redefinition_k1_partfun1)).

fof(f391,plain,
    ( ~ spl9_51
    | spl9_56
    | ~ spl9_2
    | spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f321,f218,f204,f169,f162,f155,f127,f120,f113,f106,f389,f369])).

fof(f369,plain,
    ( spl9_51
  <=> ~ v5_pre_topc(sK3,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f389,plain,
    ( spl9_56
  <=> ! [X13] :
        ( ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f120,plain,
    ( spl9_6
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f155,plain,
    ( spl9_17
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f162,plain,
    ( spl9_18
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f169,plain,
    ( spl9_20
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f321,plain,
    ( ! [X13] :
        ( ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f320,f156])).

fof(f156,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f320,plain,
    ( ! [X13] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f319,f205])).

fof(f319,plain,
    ( ! [X13] :
        ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f318,f107])).

fof(f318,plain,
    ( ! [X13] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f317,f128])).

fof(f317,plain,
    ( ! [X13] :
        ( ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f316,f121])).

fof(f121,plain,
    ( v2_pre_topc(sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f316,plain,
    ( ! [X13] :
        ( ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_5
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f315,f114])).

fof(f315,plain,
    ( ! [X13] :
        ( v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f314,f170])).

fof(f170,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f314,plain,
    ( ! [X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_18
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f310,f163])).

fof(f163,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f310,plain,
    ( ! [X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,sK3,X13)
        | ~ v5_pre_topc(sK3,sK2,sK0) )
    | ~ spl9_34 ),
    inference(resolution,[],[f80,f219])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_tmap_1(X1,X0,X2,X3)
      | ~ v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',t49_tmap_1)).

fof(f387,plain,
    ( spl9_54
    | ~ spl9_2
    | ~ spl9_22
    | ~ spl9_30
    | ~ spl9_34
    | spl9_49 ),
    inference(avatar_split_clause,[],[f367,f360,f218,f204,f176,f106,f385])).

fof(f176,plain,
    ( spl9_22
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f360,plain,
    ( spl9_49
  <=> ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f367,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_2
    | ~ spl9_22
    | ~ spl9_30
    | ~ spl9_34
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f366,f177])).

fof(f177,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f176])).

fof(f366,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_2
    | ~ spl9_30
    | ~ spl9_34
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f365,f219])).

fof(f365,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_2
    | ~ spl9_30
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f364,f205])).

fof(f364,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_2
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f363,f107])).

fof(f363,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_49 ),
    inference(resolution,[],[f361,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',dt_k3_funct_2)).

fof(f361,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f360])).

fof(f380,plain,
    ( spl9_50
    | spl9_52
    | ~ spl9_2
    | spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f297,f218,f204,f169,f162,f155,f127,f120,f113,f106,f378,f372])).

fof(f372,plain,
    ( spl9_50
  <=> v5_pre_topc(sK3,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f378,plain,
    ( spl9_52
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f297,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f296,f156])).

fof(f296,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f295,f205])).

fof(f295,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f294,f107])).

fof(f294,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f293,f128])).

fof(f293,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f292,f121])).

fof(f292,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_5
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f291,f114])).

fof(f291,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f290,f170])).

fof(f290,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_18
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f286,f163])).

fof(f286,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK0)
    | ~ spl9_34 ),
    inference(resolution,[],[f81,f219])).

fof(f81,plain,(
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
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f362,plain,
    ( ~ spl9_49
    | ~ spl9_0
    | ~ spl9_2
    | spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | spl9_11
    | ~ spl9_12
    | ~ spl9_14
    | spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_34
    | spl9_39 ),
    inference(avatar_split_clause,[],[f351,f232,f218,f211,f204,f197,f190,f183,f176,f169,f162,f155,f148,f141,f134,f127,f120,f113,f106,f99,f360])).

fof(f134,plain,
    ( spl9_11
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f141,plain,
    ( spl9_12
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f148,plain,
    ( spl9_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f183,plain,
    ( spl9_24
  <=> v5_pre_topc(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f190,plain,
    ( spl9_26
  <=> r1_tmap_1(sK2,sK0,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f351,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f350,f330])).

fof(f330,plain,
    ( ! [X14] :
        ( r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ m1_subset_1(X14,u1_struct_0(sK0)) )
    | ~ spl9_0
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f329,f184])).

fof(f184,plain,
    ( v5_pre_topc(sK4,sK0,sK1)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f183])).

fof(f329,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_0
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f328,f135])).

fof(f135,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f328,plain,
    ( ! [X14] :
        ( v2_struct_0(sK1)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_0
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f327,f198])).

fof(f327,plain,
    ( ! [X14] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_0
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f326,f100])).

fof(f326,plain,
    ( ! [X14] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f325,f170])).

fof(f325,plain,
    ( ! [X14] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f324,f163])).

fof(f324,plain,
    ( ! [X14] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f323,f156])).

fof(f323,plain,
    ( ! [X14] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f322,f149])).

fof(f149,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f322,plain,
    ( ! [X14] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_12
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f311,f142])).

fof(f142,plain,
    ( v2_pre_topc(sK1)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f311,plain,
    ( ! [X14] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X14)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl9_32 ),
    inference(resolution,[],[f80,f212])).

fof(f350,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_26
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f349,f135])).

fof(f349,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_26
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f348,f191])).

fof(f191,plain,
    ( r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f190])).

fof(f348,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f347,f177])).

fof(f347,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f346,f212])).

fof(f346,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f345,f198])).

fof(f345,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f344,f100])).

fof(f344,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_34
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f343,f219])).

fof(f343,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_30
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f342,f205])).

fof(f342,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f341,f107])).

fof(f341,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f340,f170])).

fof(f340,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f339,f163])).

fof(f339,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f338,f156])).

fof(f338,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f337,f128])).

fof(f337,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f336,f121])).

fof(f336,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_5
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f335,f114])).

fof(f335,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f334,f149])).

fof(f334,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_12
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f331,f142])).

fof(f331,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | v2_struct_0(sK1)
    | ~ spl9_39 ),
    inference(resolution,[],[f94,f233])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ r1_tmap_1(X2,X0,X4,X6)
      | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_tmap_1(X2,X0,X4,X6)
                                  & r1_tmap_1(X1,X2,X3,X5)
                                  & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6 )
                               => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',t52_tmap_1)).

fof(f307,plain,
    ( ~ spl9_45
    | spl9_46
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f237,f211,f305,f302])).

fof(f302,plain,
    ( spl9_45
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f305,plain,
    ( spl9_46
  <=> ! [X1] : ~ r2_hidden(X1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f237,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK4)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) )
    | ~ spl9_32 ),
    inference(resolution,[],[f86,f212])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',t5_subset)).

fof(f253,plain,
    ( ~ spl9_41
    | spl9_42
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f236,f218,f251,f248])).

fof(f248,plain,
    ( spl9_41
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f251,plain,
    ( spl9_42
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) )
    | ~ spl9_34 ),
    inference(resolution,[],[f86,f219])).

fof(f234,plain,(
    ~ spl9_39 ),
    inference(avatar_split_clause,[],[f60,f232])).

fof(f60,plain,(
    ~ r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
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
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( v5_pre_topc(X4,X0,X1)
                                & r1_tmap_1(X2,X0,X3,X5) )
                             => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( v5_pre_topc(X4,X0,X1)
                              & r1_tmap_1(X2,X0,X3,X5) )
                           => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',t54_tmap_1)).

fof(f227,plain,(
    spl9_36 ),
    inference(avatar_split_clause,[],[f92,f225])).

fof(f225,plain,
    ( spl9_36
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f92,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',existence_l1_pre_topc)).

fof(f220,plain,(
    spl9_34 ),
    inference(avatar_split_clause,[],[f66,f218])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f213,plain,(
    spl9_32 ),
    inference(avatar_split_clause,[],[f63,f211])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f206,plain,(
    spl9_30 ),
    inference(avatar_split_clause,[],[f65,f204])).

fof(f65,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f199,plain,(
    spl9_28 ),
    inference(avatar_split_clause,[],[f62,f197])).

fof(f62,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f192,plain,(
    spl9_26 ),
    inference(avatar_split_clause,[],[f58,f190])).

fof(f58,plain,(
    r1_tmap_1(sK2,sK0,sK3,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f185,plain,(
    spl9_24 ),
    inference(avatar_split_clause,[],[f59,f183])).

fof(f59,plain,(
    v5_pre_topc(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f178,plain,(
    spl9_22 ),
    inference(avatar_split_clause,[],[f57,f176])).

fof(f57,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f171,plain,(
    spl9_20 ),
    inference(avatar_split_clause,[],[f75,f169])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f164,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f74,f162])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f157,plain,(
    ~ spl9_17 ),
    inference(avatar_split_clause,[],[f73,f155])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f150,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f72,f148])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f143,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f71,f141])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f136,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f70,f134])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f129,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f69,f127])).

fof(f69,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f122,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f68,f120])).

fof(f68,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f67,f113])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f108,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f64,f106])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f61,f99])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
