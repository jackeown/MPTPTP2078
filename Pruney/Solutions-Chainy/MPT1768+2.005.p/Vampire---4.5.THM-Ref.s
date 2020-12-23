%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 752 expanded)
%              Number of leaves         :   50 ( 439 expanded)
%              Depth                    :    7
%              Number of atoms          :  974 (5800 expanded)
%              Number of equality atoms :   31 (  59 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f156,f174,f200,f218,f236,f250,f258,f263,f269,f278,f283,f288,f307,f312,f317,f451,f456,f457])).

fof(f457,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | k3_tmap_1(sK0,sK1,sK2,sK3,sK5) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))
    | k2_tmap_1(sK2,sK1,sK5,sK3) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))
    | k2_tmap_1(sK2,sK1,sK5,sK4) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))
    | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f456,plain,
    ( spl6_67
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f349,f285,f280,f275,f145,f140,f135,f130,f125,f120,f100,f90,f80,f453])).

fof(f453,plain,
    ( spl6_67
  <=> k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f80,plain,
    ( spl6_5
  <=> m1_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f90,plain,
    ( spl6_7
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f100,plain,
    ( spl6_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f120,plain,
    ( spl6_13
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f125,plain,
    ( spl6_14
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f130,plain,
    ( spl6_15
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f135,plain,
    ( spl6_16
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f140,plain,
    ( spl6_17
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f145,plain,
    ( spl6_18
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f275,plain,
    ( spl6_38
  <=> m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f280,plain,
    ( spl6_39
  <=> v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f285,plain,
    ( spl6_40
  <=> v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f349,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f102,f92,f82,f287,f282,f277,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f277,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f275])).

fof(f282,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f280])).

fof(f287,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f285])).

fof(f82,plain,
    ( m1_pre_topc(sK4,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f92,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f102,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f122,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f127,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f132,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f137,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f142,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f147,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f451,plain,
    ( spl6_66
    | ~ spl6_5
    | ~ spl6_6
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f350,f285,f280,f275,f255,f171,f153,f130,f125,f120,f115,f85,f80,f448])).

fof(f448,plain,
    ( spl6_66
  <=> k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f85,plain,
    ( spl6_6
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f115,plain,
    ( spl6_12
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f153,plain,
    ( spl6_19
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f171,plain,
    ( spl6_22
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f255,plain,
    ( spl6_35
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f350,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | ~ spl6_5
    | ~ spl6_6
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f117,f173,f155,f132,f127,f122,f87,f257,f82,f287,f282,f277,f54])).

fof(f257,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f255])).

fof(f87,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f155,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f173,plain,
    ( v2_pre_topc(sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f171])).

fof(f117,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f317,plain,
    ( spl6_44
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | spl6_10
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f297,f255,f171,f153,f130,f125,f120,f115,f105,f95,f85,f80,f75,f70,f65,f314])).

fof(f314,plain,
    ( spl6_44
  <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f65,plain,
    ( spl6_2
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f70,plain,
    ( spl6_3
  <=> v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f75,plain,
    ( spl6_4
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f95,plain,
    ( spl6_8
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f105,plain,
    ( spl6_10
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f297,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | spl6_10
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f117,f173,f155,f132,f127,f122,f97,f107,f82,f87,f77,f72,f67,f257,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

fof(f67,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f72,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f77,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f107,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f97,plain,
    ( ~ v2_struct_0(sK4)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f312,plain,
    ( spl6_43
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f298,f255,f145,f140,f135,f130,f125,f120,f110,f90,f75,f70,f65,f309])).

fof(f309,plain,
    ( spl6_43
  <=> k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f110,plain,
    ( spl6_11
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f298,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f112,f92,f77,f72,f67,f257,f54])).

fof(f112,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f307,plain,
    ( spl6_42
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f299,f255,f171,f153,f130,f125,f120,f115,f75,f70,f65,f304])).

fof(f304,plain,
    ( spl6_42
  <=> k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f299,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f117,f173,f155,f132,f127,f122,f77,f72,f67,f257,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f288,plain,
    ( spl6_40
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f272,f265,f197,f285])).

fof(f197,plain,
    ( spl6_26
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f265,plain,
    ( spl6_37
  <=> k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f272,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f199,f267])).

fof(f267,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f265])).

fof(f199,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f197])).

fof(f283,plain,
    ( spl6_39
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f271,f265,f215,f280])).

fof(f215,plain,
    ( spl6_29
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f271,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f217,f267])).

fof(f217,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f215])).

fof(f278,plain,
    ( spl6_38
    | ~ spl6_32
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f270,f265,f233,f275])).

fof(f233,plain,
    ( spl6_32
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f270,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_32
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f235,f267])).

fof(f235,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f233])).

fof(f269,plain,
    ( spl6_37
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f268,f260,f247,f265])).

fof(f247,plain,
    ( spl6_34
  <=> k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f260,plain,
    ( spl6_36
  <=> k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f268,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f249,f262])).

fof(f262,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f260])).

fof(f249,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f247])).

fof(f263,plain,
    ( spl6_36
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_19
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f251,f171,f153,f130,f125,f120,f115,f85,f75,f70,f65,f260])).

fof(f251,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_19
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f117,f87,f155,f132,f127,f122,f77,f72,f67,f173,f55])).

fof(f258,plain,
    ( spl6_35
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f252,f171,f153,f85,f80,f255])).

fof(f252,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f155,f82,f87,f173,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f250,plain,
    ( spl6_34
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(avatar_split_clause,[],[f243,f145,f140,f135,f130,f125,f120,f110,f100,f85,f75,f70,f65,f247])).

fof(f243,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f112,f102,f77,f87,f72,f67,f54])).

fof(f236,plain,
    ( spl6_32
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(avatar_split_clause,[],[f225,f145,f140,f135,f130,f125,f120,f110,f100,f75,f70,f65,f233])).

fof(f225,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f102,f112,f77,f72,f67,f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f218,plain,
    ( spl6_29
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(avatar_split_clause,[],[f207,f145,f140,f135,f130,f125,f120,f110,f100,f75,f70,f65,f215])).

fof(f207,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f102,f112,f77,f72,f67,f52])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f200,plain,
    ( spl6_26
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(avatar_split_clause,[],[f189,f145,f140,f135,f130,f125,f120,f110,f100,f75,f70,f65,f197])).

fof(f189,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f102,f112,f77,f72,f67,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f15])).

fof(f174,plain,
    ( spl6_22
    | ~ spl6_11
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f169,f140,f135,f110,f171])).

fof(f169,plain,
    ( v2_pre_topc(sK2)
    | ~ spl6_11
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f142,f137,f112,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f156,plain,
    ( spl6_19
    | ~ spl6_11
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f151,f135,f110,f153])).

fof(f151,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_11
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f137,f112,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f148,plain,(
    ~ spl6_18 ),
    inference(avatar_split_clause,[],[f32,f145])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f30,f29,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X3)
                        & m1_pre_topc(X3,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X3)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,X2,X3,X5)),k3_tmap_1(sK0,sK1,X2,X4,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X3)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,X2,X3,X5)),k3_tmap_1(sK0,sK1,X2,X4,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,X3)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,sK2,X3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,X3)
              & m1_pre_topc(X3,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,sK2,X3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,X3)
            & m1_pre_topc(X3,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,sK3)
          & m1_pre_topc(sK3,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_pre_topc(X4,sK3)
        & m1_pre_topc(sK3,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,sK4,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_pre_topc(sK4,sK3)
      & m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X5] :
        ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,sK4,X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
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
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X3,X2) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
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
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

fof(f143,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f33,f140])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f138,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f34,f135])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f35,f130])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f128,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f36,f125])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f123,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f37,f120])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f118,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f38,f115])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f113,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f39,f110])).

fof(f39,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f108,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f40,f105])).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f41,f100])).

fof(f41,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f44,f85])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f46,f75])).

fof(f46,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f47,f70])).

fof(f47,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f48,f65])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f49,f60])).

fof(f60,plain,
    ( spl6_1
  <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f49,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (28397)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (28405)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.48  % (28394)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.48  % (28390)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (28412)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.49  % (28392)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (28410)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (28404)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (28396)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (28395)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (28400)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (28407)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (28391)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (28393)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (28393)Refutation not found, incomplete strategy% (28393)------------------------------
% 0.21/0.50  % (28393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28393)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28393)Memory used [KB]: 10618
% 0.21/0.50  % (28393)Time elapsed: 0.091 s
% 0.21/0.50  % (28393)------------------------------
% 0.21/0.50  % (28393)------------------------------
% 0.21/0.50  % (28406)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (28402)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (28408)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (28409)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (28411)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (28399)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (28401)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (28396)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (28398)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (28400)Refutation not found, incomplete strategy% (28400)------------------------------
% 0.21/0.52  % (28400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28400)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28400)Memory used [KB]: 10618
% 0.21/0.52  % (28400)Time elapsed: 0.119 s
% 0.21/0.52  % (28400)------------------------------
% 0.21/0.52  % (28400)------------------------------
% 0.21/0.52  % (28413)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (28413)Refutation not found, incomplete strategy% (28413)------------------------------
% 0.21/0.52  % (28413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28413)Memory used [KB]: 10618
% 0.21/0.52  % (28413)Time elapsed: 0.109 s
% 0.21/0.52  % (28413)------------------------------
% 0.21/0.52  % (28413)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f458,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f156,f174,f200,f218,f236,f250,f258,f263,f269,f278,f283,f288,f307,f312,f317,f451,f456,f457])).
% 0.21/0.52  fof(f457,plain,(
% 0.21/0.52    k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | k3_tmap_1(sK0,sK1,sK2,sK3,sK5) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) | k2_tmap_1(sK2,sK1,sK5,sK3) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) | k2_tmap_1(sK2,sK1,sK5,sK4) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f456,plain,(
% 0.21/0.52    spl6_67 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_38 | ~spl6_39 | ~spl6_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f349,f285,f280,f275,f145,f140,f135,f130,f125,f120,f100,f90,f80,f453])).
% 0.21/0.52  fof(f453,plain,(
% 0.21/0.52    spl6_67 <=> k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl6_5 <=> m1_pre_topc(sK4,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl6_7 <=> m1_pre_topc(sK4,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl6_9 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl6_13 <=> l1_pre_topc(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl6_14 <=> v2_pre_topc(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl6_15 <=> v2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl6_16 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl6_17 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl6_18 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    spl6_38 <=> m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    spl6_39 <=> v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    spl6_40 <=> v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | (~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_38 | ~spl6_39 | ~spl6_40)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f102,f92,f82,f287,f282,f277,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl6_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f275])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_39),
% 0.21/0.52    inference(avatar_component_clause,[],[f280])).
% 0.21/0.52  fof(f287,plain,(
% 0.21/0.52    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~spl6_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f285])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK3) | ~spl6_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK0) | ~spl6_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK0) | ~spl6_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f100])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    l1_pre_topc(sK1) | ~spl6_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f120])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    v2_pre_topc(sK1) | ~spl6_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f125])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~v2_struct_0(sK1) | spl6_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f130])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl6_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f135])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl6_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f140])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl6_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f145])).
% 0.21/0.52  fof(f451,plain,(
% 0.21/0.52    spl6_66 | ~spl6_5 | ~spl6_6 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_19 | ~spl6_22 | ~spl6_35 | ~spl6_38 | ~spl6_39 | ~spl6_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f350,f285,f280,f275,f255,f171,f153,f130,f125,f120,f115,f85,f80,f448])).
% 0.21/0.52  fof(f448,plain,(
% 0.21/0.52    spl6_66 <=> k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl6_6 <=> m1_pre_topc(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl6_12 <=> v2_struct_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl6_19 <=> l1_pre_topc(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    spl6_22 <=> v2_pre_topc(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    spl6_35 <=> m1_pre_topc(sK4,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | (~spl6_5 | ~spl6_6 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_19 | ~spl6_22 | ~spl6_35 | ~spl6_38 | ~spl6_39 | ~spl6_40)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f117,f173,f155,f132,f127,f122,f87,f257,f82,f287,f282,f277,f54])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK2) | ~spl6_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f255])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK2) | ~spl6_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    l1_pre_topc(sK2) | ~spl6_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    v2_pre_topc(sK2) | ~spl6_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f171])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ~v2_struct_0(sK2) | spl6_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f115])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    spl6_44 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_8 | spl6_10 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_19 | ~spl6_22 | ~spl6_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f297,f255,f171,f153,f130,f125,f120,f115,f105,f95,f85,f80,f75,f70,f65,f314])).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    spl6_44 <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl6_2 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl6_3 <=> v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl6_4 <=> v1_funct_1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl6_8 <=> v2_struct_0(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl6_10 <=> v2_struct_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_8 | spl6_10 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_19 | ~spl6_22 | ~spl6_35)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f117,f173,f155,f132,f127,f122,f97,f107,f82,f87,f77,f72,f67,f257,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    v1_funct_1(sK5) | ~spl6_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~v2_struct_0(sK3) | spl6_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~v2_struct_0(sK4) | spl6_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f95])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    spl6_43 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f298,f255,f145,f140,f135,f130,f125,f120,f110,f90,f75,f70,f65,f309])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    spl6_43 <=> k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl6_11 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_35)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f112,f92,f77,f72,f67,f257,f54])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK0) | ~spl6_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f110])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    spl6_42 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_19 | ~spl6_22 | ~spl6_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f299,f255,f171,f153,f130,f125,f120,f115,f75,f70,f65,f304])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    spl6_42 <=> k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_19 | ~spl6_22 | ~spl6_35)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f117,f173,f155,f132,f127,f122,f77,f72,f67,f257,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.52  fof(f288,plain,(
% 0.21/0.52    spl6_40 | ~spl6_26 | ~spl6_37),
% 0.21/0.52    inference(avatar_split_clause,[],[f272,f265,f197,f285])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    spl6_26 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    spl6_37 <=> k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | (~spl6_26 | ~spl6_37)),
% 0.21/0.52    inference(backward_demodulation,[],[f199,f267])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) | ~spl6_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f265])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) | ~spl6_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f197])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    spl6_39 | ~spl6_29 | ~spl6_37),
% 0.21/0.52    inference(avatar_split_clause,[],[f271,f265,f215,f280])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    spl6_29 <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | (~spl6_29 | ~spl6_37)),
% 0.21/0.52    inference(backward_demodulation,[],[f217,f267])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f215])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    spl6_38 | ~spl6_32 | ~spl6_37),
% 0.21/0.52    inference(avatar_split_clause,[],[f270,f265,f233,f275])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    spl6_32 <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | (~spl6_32 | ~spl6_37)),
% 0.21/0.52    inference(backward_demodulation,[],[f235,f267])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl6_32),
% 0.21/0.52    inference(avatar_component_clause,[],[f233])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    spl6_37 | ~spl6_34 | ~spl6_36),
% 0.21/0.52    inference(avatar_split_clause,[],[f268,f260,f247,f265])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    spl6_34 <=> k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    spl6_36 <=> k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) | (~spl6_34 | ~spl6_36)),
% 0.21/0.52    inference(backward_demodulation,[],[f249,f262])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) | ~spl6_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f260])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) | ~spl6_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f247])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    spl6_36 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_19 | ~spl6_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f251,f171,f153,f130,f125,f120,f115,f85,f75,f70,f65,f260])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_19 | ~spl6_22)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f117,f87,f155,f132,f127,f122,f77,f72,f67,f173,f55])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    spl6_35 | ~spl6_5 | ~spl6_6 | ~spl6_19 | ~spl6_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f252,f171,f153,f85,f80,f255])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK2) | (~spl6_5 | ~spl6_6 | ~spl6_19 | ~spl6_22)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f155,f82,f87,f173,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    spl6_34 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f243,f145,f140,f135,f130,f125,f120,f110,f100,f85,f75,f70,f65,f247])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f112,f102,f77,f87,f72,f67,f54])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    spl6_32 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f225,f145,f140,f135,f130,f125,f120,f110,f100,f75,f70,f65,f233])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f102,f112,f77,f72,f67,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    spl6_29 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f207,f145,f140,f135,f130,f125,f120,f110,f100,f75,f70,f65,f215])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f102,f112,f77,f72,f67,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    spl6_26 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f189,f145,f140,f135,f130,f125,f120,f110,f100,f75,f70,f65,f197])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f127,f122,f102,f112,f77,f72,f67,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    spl6_22 | ~spl6_11 | ~spl6_16 | ~spl6_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f169,f140,f135,f110,f171])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    v2_pre_topc(sK2) | (~spl6_11 | ~spl6_16 | ~spl6_17)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f142,f137,f112,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl6_19 | ~spl6_11 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f151,f135,f110,f153])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    l1_pre_topc(sK2) | (~spl6_11 | ~spl6_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f137,f112,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~spl6_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f145])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    (((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f30,f29,f28,f27,f26,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,X2,X3,X5)),k3_tmap_1(sK0,sK1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,X2,X3,X5)),k3_tmap_1(sK0,sK1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,sK2,X3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,sK2,X3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,sK4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X5] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,sK4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    spl6_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f140])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl6_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f135])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ~spl6_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f130])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    spl6_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f125])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl6_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f120])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ~spl6_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f38,f115])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl6_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f110])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~spl6_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f105])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl6_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f100])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~spl6_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f95])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ~v2_struct_0(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl6_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f90])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    m1_pre_topc(sK4,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl6_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f85])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl6_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f80])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    m1_pre_topc(sK4,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl6_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f75])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v1_funct_1(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl6_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f70])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f65])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ~spl6_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl6_1 <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (28396)------------------------------
% 0.21/0.53  % (28396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28396)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (28396)Memory used [KB]: 11257
% 0.21/0.53  % (28396)Time elapsed: 0.069 s
% 0.21/0.53  % (28396)------------------------------
% 0.21/0.53  % (28396)------------------------------
% 0.21/0.53  % (28389)Success in time 0.172 s
%------------------------------------------------------------------------------
