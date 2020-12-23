%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 318 expanded)
%              Number of leaves         :   45 ( 128 expanded)
%              Depth                    :   11
%              Number of atoms          :  617 (1400 expanded)
%              Number of equality atoms :   55 ( 118 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f110,f115,f120,f130,f135,f140,f145,f150,f162,f193,f239,f262,f272,f279,f288,f302,f313,f466,f610,f1200,f1223,f1229,f1234,f1238])).

fof(f1238,plain,
    ( ~ spl5_1
    | spl5_15 ),
    inference(avatar_split_clause,[],[f1236,f159,f87])).

fof(f87,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f159,plain,
    ( spl5_15
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1236,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_15 ),
    inference(resolution,[],[f161,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f161,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f1234,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14
    | spl5_112 ),
    inference(avatar_split_clause,[],[f1232,f1226,f155,f147,f142,f137])).

fof(f137,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f142,plain,
    ( spl5_12
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f147,plain,
    ( spl5_13
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f155,plain,
    ( spl5_14
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1226,plain,
    ( spl5_112
  <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f1232,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl5_112 ),
    inference(duplicate_literal_removal,[],[f1231])).

fof(f1231,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_112 ),
    inference(resolution,[],[f1228,f85])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 != X5
      | r1_funct_2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f1228,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | spl5_112 ),
    inference(avatar_component_clause,[],[f1226])).

fof(f1229,plain,
    ( ~ spl5_112
    | spl5_35
    | ~ spl5_111 ),
    inference(avatar_split_clause,[],[f1224,f1220,f310,f1226])).

fof(f310,plain,
    ( spl5_35
  <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f1220,plain,
    ( spl5_111
  <=> sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f1224,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | spl5_35
    | ~ spl5_111 ),
    inference(backward_demodulation,[],[f312,f1222])).

fof(f1222,plain,
    ( sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f312,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f310])).

fof(f1223,plain,
    ( spl5_111
    | ~ spl5_7
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f1218,f1198,f255,f236,f117,f1220])).

fof(f117,plain,
    ( spl5_7
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f236,plain,
    ( spl5_25
  <=> sK3 = k7_relat_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f255,plain,
    ( spl5_27
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f1198,plain,
    ( spl5_108
  <=> ! [X0] :
        ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f1218,plain,
    ( sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ spl5_7
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_108 ),
    inference(forward_demodulation,[],[f1217,f238])).

fof(f238,plain,
    ( sK3 = k7_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f236])).

fof(f1217,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl5_7
    | ~ spl5_27
    | ~ spl5_108 ),
    inference(forward_demodulation,[],[f1204,f257])).

fof(f257,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f255])).

fof(f1204,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl5_7
    | ~ spl5_108 ),
    inference(resolution,[],[f1199,f119])).

fof(f119,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f1199,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) )
    | ~ spl5_108 ),
    inference(avatar_component_clause,[],[f1198])).

fof(f1200,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_108
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_73 ),
    inference(avatar_split_clause,[],[f1196,f608,f147,f137,f1198,f142,f137])).

fof(f608,plain,
    ( spl5_73
  <=> ! [X3,X2] :
        ( k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f1196,plain,
    ( ! [X0] :
        ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_73 ),
    inference(forward_demodulation,[],[f1195,f372])).

fof(f372,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0)
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(resolution,[],[f244,f139])).

fof(f139,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl5_13 ),
    inference(resolution,[],[f77,f149])).

fof(f149,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f1195,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl5_13
    | ~ spl5_73 ),
    inference(resolution,[],[f609,f149])).

fof(f609,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f608])).

fof(f610,plain,
    ( ~ spl5_4
    | spl5_6
    | spl5_73
    | ~ spl5_5
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f602,f464,f107,f608,f112,f102])).

fof(f102,plain,
    ( spl5_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f112,plain,
    ( spl5_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f107,plain,
    ( spl5_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f464,plain,
    ( spl5_54
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f602,plain,
    ( ! [X2,X3] :
        ( k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_5
    | ~ spl5_54 ),
    inference(resolution,[],[f465,f109])).

fof(f109,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f465,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f464])).

fof(f466,plain,
    ( ~ spl5_1
    | spl5_3
    | spl5_54
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f457,f92,f464,f97,f87])).

fof(f97,plain,
    ( spl5_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f457,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X2,X0)
        | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f65,f94])).

fof(f94,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f313,plain,
    ( ~ spl5_35
    | spl5_9
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f306,f255,f127,f310])).

fof(f127,plain,
    ( spl5_9
  <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f306,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl5_9
    | ~ spl5_27 ),
    inference(backward_demodulation,[],[f129,f257])).

fof(f129,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f302,plain,
    ( ~ spl5_4
    | spl5_32 ),
    inference(avatar_split_clause,[],[f299,f285,f102])).

fof(f285,plain,
    ( spl5_32
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f299,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_32 ),
    inference(resolution,[],[f287,f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f287,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl5_32 ),
    inference(avatar_component_clause,[],[f285])).

fof(f288,plain,
    ( ~ spl5_32
    | ~ spl5_4
    | spl5_31 ),
    inference(avatar_split_clause,[],[f283,f276,f102,f285])).

fof(f276,plain,
    ( spl5_31
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f283,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | spl5_31 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | spl5_31 ),
    inference(resolution,[],[f278,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f278,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f276])).

fof(f279,plain,
    ( ~ spl5_20
    | ~ spl5_31
    | ~ spl5_10
    | spl5_30 ),
    inference(avatar_split_clause,[],[f274,f269,f132,f276,f187])).

fof(f187,plain,
    ( spl5_20
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f132,plain,
    ( spl5_10
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f269,plain,
    ( spl5_30
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f274,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ spl5_10
    | spl5_30 ),
    inference(forward_demodulation,[],[f273,f134])).

fof(f134,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f273,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl5_30 ),
    inference(resolution,[],[f271,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f271,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f269])).

fof(f272,plain,
    ( ~ spl5_20
    | ~ spl5_30
    | spl5_28 ),
    inference(avatar_split_clause,[],[f267,f259,f269,f187])).

fof(f259,plain,
    ( spl5_28
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f267,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2)
    | spl5_28 ),
    inference(resolution,[],[f261,f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f200,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f195,f56])).

fof(f56,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f195,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f66,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f261,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f259])).

fof(f262,plain,
    ( spl5_27
    | ~ spl5_28
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f251,f117,f102,f259,f255])).

fof(f251,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(resolution,[],[f242,f119])).

fof(f242,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK1)
        | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X4))
        | u1_struct_0(sK1) = u1_struct_0(X4) )
    | ~ spl5_4 ),
    inference(resolution,[],[f220,f104])).

fof(f104,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(resolution,[],[f202,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f239,plain,
    ( spl5_25
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f234,f137,f236])).

fof(f234,plain,
    ( sK3 = k7_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl5_11 ),
    inference(resolution,[],[f233,f139])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k7_relat_1(X0,X1) = X0 ) ),
    inference(condensation,[],[f232])).

fof(f232,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f199,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f199,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f67,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f193,plain,
    ( ~ spl5_4
    | ~ spl5_7
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_7
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f104,f119,f189,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f189,plain,
    ( ~ l1_pre_topc(sK2)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f187])).

fof(f162,plain,
    ( ~ spl5_14
    | ~ spl5_15
    | spl5_3 ),
    inference(avatar_split_clause,[],[f151,f97,f159,f155])).

fof(f151,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_3 ),
    inference(resolution,[],[f64,f99])).

fof(f99,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f64,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f150,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f43,f147])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

fof(f145,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f44,f142])).

fof(f44,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f140,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f45,f137])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f135,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f46,f132])).

fof(f46,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f130,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f47,f127])).

fof(f47,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f49,f117])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f115,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f50,f112])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f110,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f51,f107])).

fof(f51,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f53,f97])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f54,f92])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f55,f87])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (4015)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (4007)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (4007)Refutation not found, incomplete strategy% (4007)------------------------------
% 0.21/0.48  % (4007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4007)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (4007)Memory used [KB]: 1791
% 0.21/0.49  % (4007)Time elapsed: 0.007 s
% 0.21/0.49  % (4007)------------------------------
% 0.21/0.49  % (4007)------------------------------
% 0.21/0.49  % (4004)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (4012)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (4006)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (4015)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1239,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f110,f115,f120,f130,f135,f140,f145,f150,f162,f193,f239,f262,f272,f279,f288,f302,f313,f466,f610,f1200,f1223,f1229,f1234,f1238])).
% 0.21/0.50  fof(f1238,plain,(
% 0.21/0.50    ~spl5_1 | spl5_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f1236,f159,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl5_1 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl5_15 <=> l1_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.50  fof(f1236,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | spl5_15),
% 0.21/0.50    inference(resolution,[],[f161,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~l1_struct_0(sK0) | spl5_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f159])).
% 0.21/0.50  fof(f1234,plain,(
% 0.21/0.50    ~spl5_11 | ~spl5_12 | ~spl5_13 | spl5_14 | spl5_112),
% 0.21/0.50    inference(avatar_split_clause,[],[f1232,f1226,f155,f147,f142,f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl5_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl5_12 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl5_13 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl5_14 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.50  fof(f1226,plain,(
% 0.21/0.50    spl5_112 <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).
% 0.21/0.50  fof(f1232,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl5_112),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f1231])).
% 0.21/0.50  fof(f1231,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK0)) | spl5_112),
% 0.21/0.50    inference(resolution,[],[f1228,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | v1_xboole_0(X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5)) )),
% 0.21/0.50    inference(equality_resolution,[],[f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 != X5 | r1_funct_2(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.21/0.50    inference(flattening,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.21/0.50  fof(f1228,plain,(
% 0.21/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | spl5_112),
% 0.21/0.50    inference(avatar_component_clause,[],[f1226])).
% 0.21/0.50  fof(f1229,plain,(
% 0.21/0.50    ~spl5_112 | spl5_35 | ~spl5_111),
% 0.21/0.50    inference(avatar_split_clause,[],[f1224,f1220,f310,f1226])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    spl5_35 <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.50  fof(f1220,plain,(
% 0.21/0.50    spl5_111 <=> sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).
% 0.21/0.50  fof(f1224,plain,(
% 0.21/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | (spl5_35 | ~spl5_111)),
% 0.21/0.50    inference(backward_demodulation,[],[f312,f1222])).
% 0.21/0.50  fof(f1222,plain,(
% 0.21/0.50    sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) | ~spl5_111),
% 0.21/0.50    inference(avatar_component_clause,[],[f1220])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | spl5_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f310])).
% 0.21/0.50  fof(f1223,plain,(
% 0.21/0.50    spl5_111 | ~spl5_7 | ~spl5_25 | ~spl5_27 | ~spl5_108),
% 0.21/0.50    inference(avatar_split_clause,[],[f1218,f1198,f255,f236,f117,f1220])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl5_7 <=> m1_pre_topc(sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    spl5_25 <=> sK3 = k7_relat_1(sK3,u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    spl5_27 <=> u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.50  fof(f1198,plain,(
% 0.21/0.50    spl5_108 <=> ! [X0] : (k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).
% 0.21/0.50  fof(f1218,plain,(
% 0.21/0.50    sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) | (~spl5_7 | ~spl5_25 | ~spl5_27 | ~spl5_108)),
% 0.21/0.50    inference(forward_demodulation,[],[f1217,f238])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    sK3 = k7_relat_1(sK3,u1_struct_0(sK1)) | ~spl5_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f236])).
% 0.21/0.50  fof(f1217,plain,(
% 0.21/0.50    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK1)) | (~spl5_7 | ~spl5_27 | ~spl5_108)),
% 0.21/0.50    inference(forward_demodulation,[],[f1204,f257])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl5_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f255])).
% 0.21/0.50  fof(f1204,plain,(
% 0.21/0.50    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | (~spl5_7 | ~spl5_108)),
% 0.21/0.50    inference(resolution,[],[f1199,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK1) | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f1199,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))) ) | ~spl5_108),
% 0.21/0.50    inference(avatar_component_clause,[],[f1198])).
% 0.21/0.50  fof(f1200,plain,(
% 0.21/0.50    ~spl5_11 | ~spl5_12 | spl5_108 | ~spl5_11 | ~spl5_13 | ~spl5_73),
% 0.21/0.50    inference(avatar_split_clause,[],[f1196,f608,f147,f137,f1198,f142,f137])).
% 0.21/0.50  fof(f608,plain,(
% 0.21/0.50    spl5_73 <=> ! [X3,X2] : (k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.21/0.50  fof(f1196,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1)) ) | (~spl5_11 | ~spl5_13 | ~spl5_73)),
% 0.21/0.50    inference(forward_demodulation,[],[f1195,f372])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0)) ) | (~spl5_11 | ~spl5_13)),
% 0.21/0.50    inference(resolution,[],[f244,f139])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl5_13),
% 0.21/0.50    inference(resolution,[],[f77,f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl5_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f147])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.50  fof(f1195,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1)) ) | (~spl5_13 | ~spl5_73)),
% 0.21/0.50    inference(resolution,[],[f609,f149])).
% 0.21/0.50  fof(f609,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,sK1)) ) | ~spl5_73),
% 0.21/0.50    inference(avatar_component_clause,[],[f608])).
% 0.21/0.50  fof(f610,plain,(
% 0.21/0.50    ~spl5_4 | spl5_6 | spl5_73 | ~spl5_5 | ~spl5_54),
% 0.21/0.50    inference(avatar_split_clause,[],[f602,f464,f107,f608,f112,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl5_4 <=> l1_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl5_6 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl5_5 <=> v2_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f464,plain,(
% 0.21/0.50    spl5_54 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.21/0.50  fof(f602,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK1)) ) | (~spl5_5 | ~spl5_54)),
% 0.21/0.50    inference(resolution,[],[f465,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    v2_pre_topc(sK1) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f107])).
% 0.21/0.50  fof(f465,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | v2_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl5_54),
% 0.21/0.50    inference(avatar_component_clause,[],[f464])).
% 0.21/0.50  fof(f466,plain,(
% 0.21/0.50    ~spl5_1 | spl5_3 | spl5_54 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f457,f92,f464,f97,f87])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl5_3 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl5_2 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))) ) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f65,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    v2_pre_topc(sK0) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f92])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    ~spl5_35 | spl5_9 | ~spl5_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f306,f255,f127,f310])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl5_9 <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | (spl5_9 | ~spl5_27)),
% 0.21/0.50    inference(backward_demodulation,[],[f129,f257])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f127])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    ~spl5_4 | spl5_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f299,f285,f102])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    spl5_32 <=> m1_pre_topc(sK1,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | spl5_32),
% 0.21/0.50    inference(resolution,[],[f287,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    ~m1_pre_topc(sK1,sK1) | spl5_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f285])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    ~spl5_32 | ~spl5_4 | spl5_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f283,f276,f102,f285])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl5_31 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | spl5_31),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f281])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | spl5_31),
% 0.21/0.50    inference(resolution,[],[f278,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f276])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    ~spl5_20 | ~spl5_31 | ~spl5_10 | spl5_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f274,f269,f132,f276,f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl5_20 <=> l1_pre_topc(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl5_10 <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    spl5_30 <=> m1_pre_topc(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK2) | (~spl5_10 | spl5_30)),
% 0.21/0.50    inference(forward_demodulation,[],[f273,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | spl5_30),
% 0.21/0.50    inference(resolution,[],[f271,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    ~m1_pre_topc(sK1,sK2) | spl5_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f269])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    ~spl5_20 | ~spl5_30 | spl5_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f267,f259,f269,f187])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    spl5_28 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ~m1_pre_topc(sK1,sK2) | ~l1_pre_topc(sK2) | spl5_28),
% 0.21/0.50    inference(resolution,[],[f261,f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.50    inference(resolution,[],[f200,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f195,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f66,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | spl5_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f259])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    spl5_27 | ~spl5_28 | ~spl5_4 | ~spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f251,f117,f102,f259,f255])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | u1_struct_0(sK1) = u1_struct_0(sK2) | (~spl5_4 | ~spl5_7)),
% 0.21/0.50    inference(resolution,[],[f242,f119])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ( ! [X4] : (~m1_pre_topc(X4,sK1) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(X4)) | u1_struct_0(sK1) = u1_struct_0(X4)) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f220,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    l1_pre_topc(sK1) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(X1)) )),
% 0.21/0.50    inference(resolution,[],[f202,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    spl5_25 | ~spl5_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f234,f137,f236])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    sK3 = k7_relat_1(sK3,u1_struct_0(sK1)) | ~spl5_11),
% 0.21/0.50    inference(resolution,[],[f233,f139])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k7_relat_1(X0,X1) = X0) )),
% 0.21/0.50    inference(condensation,[],[f232])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.21/0.50    inference(resolution,[],[f199,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.50    inference(resolution,[],[f67,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ~spl5_4 | ~spl5_7 | spl5_20),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    $false | (~spl5_4 | ~spl5_7 | spl5_20)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f104,f119,f189,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ~l1_pre_topc(sK2) | spl5_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f187])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ~spl5_14 | ~spl5_15 | spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f151,f97,f159,f155])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0)) | spl5_3),
% 0.21/0.50    inference(resolution,[],[f64,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl5_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f147])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f18])).
% 0.21/0.50  fof(f18,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f142])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl5_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f137])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f132])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f127])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f117])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ~spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f112])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f107])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f102])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ~spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f97])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f92])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f87])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (4015)------------------------------
% 0.21/0.51  % (4015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4015)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (4015)Memory used [KB]: 7036
% 0.21/0.51  % (4015)Time elapsed: 0.031 s
% 0.21/0.51  % (4015)------------------------------
% 0.21/0.51  % (4015)------------------------------
% 0.21/0.51  % (4021)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (3996)Success in time 0.15 s
%------------------------------------------------------------------------------
