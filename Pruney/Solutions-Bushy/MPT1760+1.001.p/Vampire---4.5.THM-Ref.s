%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1760+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:30 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 589 expanded)
%              Number of leaves         :   54 ( 332 expanded)
%              Depth                    :    7
%              Number of atoms          :  993 (8161 expanded)
%              Number of equality atoms :    8 (  26 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f773,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f99,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f174,f179,f184,f189,f194,f199,f207,f212,f217,f229,f235,f265,f304,f361,f381,f406,f483,f716,f744,f752,f758,f761,f762,f768,f772])).

fof(f772,plain,
    ( ~ spl8_27
    | ~ spl8_29
    | ~ spl8_60
    | ~ spl8_114
    | ~ spl8_71
    | ~ spl8_37
    | spl8_117 ),
    inference(avatar_split_clause,[],[f771,f765,f262,f480,f741,f403,f214,f204])).

fof(f204,plain,
    ( spl8_27
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f214,plain,
    ( spl8_29
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f403,plain,
    ( spl8_60
  <=> v1_funct_1(k5_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f741,plain,
    ( spl8_114
  <=> v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f480,plain,
    ( spl8_71
  <=> m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f262,plain,
    ( spl8_37
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f765,plain,
    ( spl8_117
  <=> m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f771,plain,
    ( ~ l1_struct_0(sK3)
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | spl8_117 ),
    inference(resolution,[],[f767,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f767,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | spl8_117 ),
    inference(avatar_component_clause,[],[f765])).

fof(f768,plain,
    ( ~ spl8_117
    | spl8_4
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f763,f358,f86,f765])).

fof(f86,plain,
    ( spl8_4
  <=> m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f358,plain,
    ( spl8_52
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4) = k5_relat_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f763,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | spl8_4
    | ~ spl8_52 ),
    inference(forward_demodulation,[],[f88,f360])).

fof(f360,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4) = k5_relat_1(sK5,sK4)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f358])).

fof(f88,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f762,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4) != k5_relat_1(sK5,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f761,plain,
    ( ~ spl8_27
    | ~ spl8_29
    | ~ spl8_60
    | ~ spl8_114
    | ~ spl8_71
    | ~ spl8_37
    | spl8_116 ),
    inference(avatar_split_clause,[],[f760,f755,f262,f480,f741,f403,f214,f204])).

fof(f755,plain,
    ( spl8_116
  <=> v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f760,plain,
    ( ~ l1_struct_0(sK3)
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | spl8_116 ),
    inference(resolution,[],[f757,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f757,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | spl8_116 ),
    inference(avatar_component_clause,[],[f755])).

fof(f758,plain,
    ( ~ spl8_116
    | spl8_2
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f753,f358,f78,f755])).

fof(f78,plain,
    ( spl8_2
  <=> v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f753,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | spl8_2
    | ~ spl8_52 ),
    inference(forward_demodulation,[],[f80,f360])).

fof(f80,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f752,plain,
    ( ~ spl8_27
    | ~ spl8_29
    | ~ spl8_60
    | ~ spl8_114
    | ~ spl8_71
    | ~ spl8_37
    | spl8_56 ),
    inference(avatar_split_clause,[],[f751,f378,f262,f480,f741,f403,f214,f204])).

fof(f378,plain,
    ( spl8_56
  <=> v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f751,plain,
    ( ~ l1_struct_0(sK3)
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | spl8_56 ),
    inference(resolution,[],[f380,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f380,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | spl8_56 ),
    inference(avatar_component_clause,[],[f378])).

fof(f744,plain,
    ( spl8_114
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | spl8_32 ),
    inference(avatar_split_clause,[],[f721,f232,f141,f136,f126,f121,f116,f111,f741])).

fof(f111,plain,
    ( spl8_9
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f116,plain,
    ( spl8_10
  <=> v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f121,plain,
    ( spl8_11
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f126,plain,
    ( spl8_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f136,plain,
    ( spl8_14
  <=> v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f141,plain,
    ( spl8_15
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f232,plain,
    ( spl8_32
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f721,plain,
    ( v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | spl8_32 ),
    inference(unit_resulting_resolution,[],[f143,f123,f118,f113,f138,f128,f234,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_2)).

fof(f234,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f232])).

fof(f128,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f138,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f113,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( v1_funct_1(sK5)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f143,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f716,plain,
    ( spl8_109
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | spl8_23
    | ~ spl8_24
    | ~ spl8_25
    | spl8_26
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f711,f358,f196,f191,f186,f181,f176,f171,f166,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f111,f96,f713])).

fof(f713,plain,
    ( spl8_109
  <=> v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f96,plain,
    ( spl8_6
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f131,plain,
    ( spl8_13
  <=> v5_pre_topc(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f146,plain,
    ( spl8_16
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f151,plain,
    ( spl8_17
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f156,plain,
    ( spl8_18
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f161,plain,
    ( spl8_19
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f166,plain,
    ( spl8_20
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f171,plain,
    ( spl8_21
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f176,plain,
    ( spl8_22
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f181,plain,
    ( spl8_23
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f186,plain,
    ( spl8_24
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f191,plain,
    ( spl8_25
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

% (18559)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f196,plain,
    ( spl8_26
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f711,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | spl8_23
    | ~ spl8_24
    | ~ spl8_25
    | spl8_26
    | ~ spl8_52 ),
    inference(forward_demodulation,[],[f709,f360])).

fof(f709,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | spl8_23
    | ~ spl8_24
    | ~ spl8_25
    | spl8_26 ),
    inference(unit_resulting_resolution,[],[f198,f193,f188,f183,f178,f173,f168,f163,f158,f153,f123,f143,f148,f133,f138,f128,f118,f98,f113,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_pre_topc(X3,X0)
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
      | ~ v5_pre_topc(X4,X1,X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          | ~ v5_pre_topc(X4,X1,X2)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          | ~ v5_pre_topc(X4,X1,X2)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                              & v5_pre_topc(X4,X1,X2) )
                           => v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tmap_1)).

fof(f98,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f133,plain,
    ( v5_pre_topc(sK4,sK1,sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f148,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f153,plain,
    ( ~ v2_struct_0(sK3)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f158,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f163,plain,
    ( v2_pre_topc(sK2)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f168,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f173,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f171])).

fof(f178,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f176])).

fof(f183,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f188,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f193,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f191])).

fof(f198,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f196])).

fof(f483,plain,
    ( spl8_71
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_15
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f478,f358,f141,f126,f121,f111,f480])).

fof(f478,plain,
    ( m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_15
    | ~ spl8_52 ),
    inference(forward_demodulation,[],[f440,f360])).

fof(f440,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f123,f143,f113,f128,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f406,plain,
    ( spl8_60
    | ~ spl8_43
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f400,f358,f301,f403])).

fof(f301,plain,
    ( spl8_43
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f400,plain,
    ( v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ spl8_43
    | ~ spl8_52 ),
    inference(backward_demodulation,[],[f303,f360])).

fof(f303,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f301])).

fof(f381,plain,
    ( ~ spl8_11
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_12
    | ~ spl8_56
    | spl8_1 ),
    inference(avatar_split_clause,[],[f329,f74,f378,f126,f141,f111,f121])).

% (18574)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (18576)Refutation not found, incomplete strategy% (18576)------------------------------
% (18576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f74,plain,
    ( spl8_1
  <=> v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f329,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | spl8_1 ),
    inference(superposition,[],[f76,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f76,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f361,plain,
    ( spl8_52
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f323,f141,f126,f121,f111,f358])).

fof(f323,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4) = k5_relat_1(sK5,sK4)
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f123,f143,f113,f128,f59])).

fof(f304,plain,
    ( spl8_43
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f269,f141,f126,f121,f111,f301])).

fof(f269,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4))
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f123,f143,f113,f128,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f265,plain,
    ( spl8_37
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f260,f226,f262])).

fof(f226,plain,
    ( spl8_31
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f260,plain,
    ( l1_struct_0(sK3)
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f228,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f228,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f226])).

fof(f235,plain,
    ( ~ spl8_32
    | spl8_23
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f230,f209,f181,f232])).

fof(f209,plain,
    ( spl8_28
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f230,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl8_23
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f183,f211,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f211,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f209])).

fof(f229,plain,
    ( spl8_31
    | ~ spl8_16
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f224,f186,f146,f226])).

fof(f224,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_16
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f188,f148,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f217,plain,
    ( spl8_29
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f200,f156,f214])).

fof(f200,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f158,f68])).

fof(f212,plain,
    ( spl8_28
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f201,f171,f209])).

fof(f201,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f173,f68])).

fof(f207,plain,
    ( spl8_27
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f202,f186,f204])).

fof(f202,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f188,f68])).

fof(f199,plain,(
    ~ spl8_26 ),
    inference(avatar_split_clause,[],[f34,f196])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) )
    & m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
    & v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v5_pre_topc(sK4,sK1,sK2)
    & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f32,f31,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                              | ~ v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                              | ~ v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                              | ~ v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                            & m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X5,X3))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X4,X1,X2)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
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
                          ( ( ~ m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            | ~ v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                            | ~ v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                            | ~ v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                          & m1_subset_1(k2_tmap_1(sK0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK0,X1,X5,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK0,X1,X5,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X4,X1,X2)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                          | ~ v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                          | ~ v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                          | ~ v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                        & m1_subset_1(k2_tmap_1(sK0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK0,X1,X5,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK0,X1,X5,X3))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v5_pre_topc(X4,X1,X2)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                        | ~ v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                        | ~ v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                        | ~ v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3)) )
                      & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1)
                      & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                  & v5_pre_topc(X4,sK1,X2)
                  & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                      | ~ v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                      | ~ v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                      | ~ v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3)) )
                    & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1)
                    & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                & v5_pre_topc(X4,sK1,X2)
                & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X2))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),X3,sK2)
                    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(sK2))
                    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3)) )
                  & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1)
                  & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
              & v5_pre_topc(X4,sK1,sK2)
              & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                  | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),X3,sK2)
                  | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(sK2))
                  | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3)) )
                & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1)
                & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
            & v5_pre_topc(X4,sK1,sK2)
            & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),sK3,sK2)
                | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
                | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3)) )
              & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1)
              & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v5_pre_topc(X4,sK1,sK2)
          & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),sK3,sK2)
              | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
              | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3)) )
            & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1)
            & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v5_pre_topc(X4,sK1,sK2)
        & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),sK3,sK2)
            | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
            | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3)) )
          & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1)
          & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v5_pre_topc(sK4,sK1,sK2)
      & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),sK3,sK2)
          | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
          | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3)) )
        & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1)
        & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) )
      & m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
      & v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                            | ~ v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                            | ~ v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                          & m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X5,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X4,X1,X2)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                            | ~ v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                            | ~ v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                          & m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X5,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X4,X1,X2)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          & v5_pre_topc(X4,X1,X2)
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                                & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(k2_tmap_1(X0,X1,X5,X3)) )
                             => ( m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                                & v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                                & v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                                & v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

% (18576)Termination reason: Refutation not found, incomplete strategy

% (18576)Memory used [KB]: 10746
% (18576)Time elapsed: 0.053 s
% (18576)------------------------------
% (18576)------------------------------
fof(f9,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X4,X1,X2)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X5,X3)) )
                           => ( m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                              & v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                              & v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                              & v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tmap_1)).

fof(f194,plain,(
    spl8_25 ),
    inference(avatar_split_clause,[],[f35,f191])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f189,plain,(
    spl8_24 ),
    inference(avatar_split_clause,[],[f36,f186])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f184,plain,(
    ~ spl8_23 ),
    inference(avatar_split_clause,[],[f37,f181])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f179,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f38,f176])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f174,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f39,f171])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f169,plain,(
    ~ spl8_20 ),
    inference(avatar_split_clause,[],[f40,f166])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f164,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f41,f161])).

fof(f41,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f159,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f42,f156])).

fof(f42,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f154,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f43,f151])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f149,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f44,f146])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f144,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f45,f141])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f139,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f46,f136])).

fof(f46,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f134,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f47,f131])).

fof(f47,plain,(
    v5_pre_topc(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f48,f126])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f49,f121])).

fof(f49,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f119,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f50,f116])).

fof(f50,plain,(
    v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f114,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f54,f96])).

fof(f54,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f56,f86,f82,f78,f74])).

fof(f82,plain,
    ( spl8_3
  <=> v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
