%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:34 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 430 expanded)
%              Number of leaves         :   39 ( 190 expanded)
%              Depth                    :   17
%              Number of atoms          :  925 (2084 expanded)
%              Number of equality atoms :  141 ( 344 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f968,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f95,f96,f106,f111,f116,f145,f163,f183,f203,f208,f306,f327,f466,f469,f515,f526,f555,f570,f575,f600,f601,f769,f840,f883,f937,f967])).

fof(f967,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17
    | spl4_30
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17
    | spl4_30
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f965,f91])).

fof(f91,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_3
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f965,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17
    | spl4_30
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f964,f326])).

fof(f326,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl4_34
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f964,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17
    | spl4_30 ),
    inference(unit_resulting_resolution,[],[f115,f110,f105,f182,f300,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

% (7305)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f300,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl4_30
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f182,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_17
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f110,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f115,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f937,plain,
    ( ~ spl4_30
    | spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f936,f160,f103,f86,f82,f299])).

fof(f82,plain,
    ( spl4_1
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f86,plain,
    ( spl4_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f160,plain,
    ( spl4_14
  <=> u1_struct_0(sK1) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f936,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f935,f105])).

fof(f935,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f934,f87])).

fof(f87,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f934,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f603,f84])).

fof(f84,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f603,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_14 ),
    inference(superposition,[],[f68,f162])).

fof(f162,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK3(X0,X1),X0)
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0,X1),X0)
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f883,plain,
    ( spl4_3
    | ~ spl4_34
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f860,f512,f324,f90])).

fof(f512,plain,
    ( spl4_59
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f860,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl4_34
    | ~ spl4_59 ),
    inference(backward_demodulation,[],[f514,f326])).

fof(f514,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f512])).

fof(f840,plain,
    ( spl4_34
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_66
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f839,f766,f572,f567,f552,f113,f108,f103,f86,f324])).

fof(f552,plain,
    ( spl4_62
  <=> v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f567,plain,
    ( spl4_65
  <=> l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f572,plain,
    ( spl4_66
  <=> v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f766,plain,
    ( spl4_86
  <=> u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f839,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_66
    | ~ spl4_86 ),
    inference(trivial_inequality_removal,[],[f838])).

fof(f838,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_66
    | ~ spl4_86 ),
    inference(forward_demodulation,[],[f837,f768])).

fof(f768,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f766])).

fof(f837,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1))))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f836,f569])).

fof(f569,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f567])).

fof(f836,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1))))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f826,f574])).

fof(f574,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f572])).

fof(f826,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1))))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62 ),
    inference(resolution,[],[f262,f554])).

fof(f554,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f552])).

fof(f262,plain,
    ( ! [X7] :
        ( ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | k6_tmap_1(sK0,sK2(sK0,sK1,X7)) != X7
        | k8_tmap_1(sK0,sK1) = X7 )
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(resolution,[],[f155,f87])).

fof(f155,plain,
    ( ! [X4,X3] :
        ( ~ v1_pre_topc(X4)
        | ~ m1_pre_topc(X3,sK0)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | k6_tmap_1(sK0,sK2(sK0,X3,X4)) != X4
        | k8_tmap_1(sK0,X3) = X4 )
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f154,f110])).

fof(f154,plain,
    ( ! [X4,X3] :
        ( k6_tmap_1(sK0,sK2(sK0,X3,X4)) != X4
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ v1_pre_topc(X4)
        | ~ m1_pre_topc(X3,sK0)
        | ~ v2_pre_topc(sK0)
        | k8_tmap_1(sK0,X3) = X4 )
    | ~ spl4_5
    | spl4_7 ),
    inference(subsumption_resolution,[],[f148,f105])).

fof(f148,plain,
    ( ! [X4,X3] :
        ( k6_tmap_1(sK0,sK2(sK0,X3,X4)) != X4
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ v1_pre_topc(X4)
        | ~ m1_pre_topc(X3,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k8_tmap_1(sK0,X3) = X4 )
    | spl4_7 ),
    inference(resolution,[],[f115,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k8_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK2(X0,X1,X2)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
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
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f769,plain,
    ( spl4_34
    | spl4_86
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f764,f572,f567,f552,f113,f108,f103,f86,f766,f324])).

fof(f764,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62
    | ~ spl4_65
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f763,f569])).

fof(f763,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f751,f574])).

fof(f751,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_62 ),
    inference(resolution,[],[f232,f554])).

fof(f232,plain,
    ( ! [X7] :
        ( ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | u1_struct_0(sK1) = sK2(sK0,sK1,X7)
        | k8_tmap_1(sK0,sK1) = X7 )
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(resolution,[],[f153,f87])).

fof(f153,plain,
    ( ! [X2,X1] :
        ( ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | u1_struct_0(X1) = sK2(sK0,X1,X2)
        | k8_tmap_1(sK0,X1) = X2 )
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f152,f110])).

fof(f152,plain,
    ( ! [X2,X1] :
        ( u1_struct_0(X1) = sK2(sK0,X1,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0)
        | k8_tmap_1(sK0,X1) = X2 )
    | ~ spl4_5
    | spl4_7 ),
    inference(subsumption_resolution,[],[f147,f105])).

fof(f147,plain,
    ( ! [X2,X1] :
        ( u1_struct_0(X1) = sK2(sK0,X1,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k8_tmap_1(sK0,X1) = X2 )
    | spl4_7 ),
    inference(resolution,[],[f115,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | u1_struct_0(X1) = sK2(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k8_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f601,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f600,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f575,plain,
    ( spl4_66
    | ~ spl4_36
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f534,f512,f337,f572])).

fof(f337,plain,
    ( spl4_36
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f534,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_36
    | ~ spl4_59 ),
    inference(backward_demodulation,[],[f338,f514])).

fof(f338,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f337])).

fof(f570,plain,
    ( spl4_65
    | ~ spl4_35
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f533,f512,f333,f567])).

fof(f333,plain,
    ( spl4_35
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f533,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_35
    | ~ spl4_59 ),
    inference(backward_demodulation,[],[f334,f514])).

fof(f334,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f333])).

fof(f555,plain,
    ( spl4_62
    | ~ spl4_19
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f530,f512,f205,f552])).

fof(f205,plain,
    ( spl4_19
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f530,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_19
    | ~ spl4_59 ),
    inference(backward_demodulation,[],[f207,f514])).

fof(f207,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f205])).

fof(f526,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f515,plain,
    ( spl4_59
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f510,f299,f180,f113,f108,f103,f512])).

fof(f510,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f505,f301])).

fof(f301,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f299])).

fof(f505,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17 ),
    inference(resolution,[],[f150,f182])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X0) )
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f149,f110])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X0) )
    | ~ spl4_5
    | spl4_7 ),
    inference(subsumption_resolution,[],[f146,f105])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X0) )
    | spl4_7 ),
    inference(resolution,[],[f115,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f469,plain,
    ( spl4_35
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f443,f200,f103,f333])).

fof(f200,plain,
    ( spl4_18
  <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f443,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f105,f202,f69])).

fof(f69,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f202,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f466,plain,
    ( spl4_36
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f445,f200,f108,f103,f337])).

fof(f445,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f110,f105,f202,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f327,plain,
    ( ~ spl4_31
    | ~ spl4_32
    | ~ spl4_33
    | spl4_34
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f310,f180,f113,f108,f103,f86,f324,f320,f316,f312])).

fof(f312,plain,
    ( spl4_31
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f316,plain,
    ( spl4_32
  <=> v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f320,plain,
    ( spl4_33
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f310,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f309,f115])).

fof(f309,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f308,f110])).

fof(f308,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f307,f105])).

fof(f307,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f297,f87])).

fof(f297,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f182,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f306,plain,
    ( spl4_30
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f305,f180,f103,f86,f82,f299])).

fof(f305,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f304,f105])).

fof(f304,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f303,f87])).

fof(f303,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f296,f83])).

fof(f83,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f296,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f182,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f208,plain,
    ( spl4_19
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f197,f142,f103,f205])).

fof(f142,plain,
    ( spl4_13
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f197,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f105,f144,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f144,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f203,plain,
    ( spl4_18
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f198,f142,f103,f200])).

fof(f198,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f105,f144,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f183,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f166,f103,f86,f180])).

fof(f166,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f105,f87,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f163,plain,
    ( spl4_14
    | spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f158,f103,f86,f82,f160])).

fof(f158,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f157,f105])).

fof(f157,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f156,f87])).

fof(f156,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_1 ),
    inference(resolution,[],[f84,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f145,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f140,f103,f142])).

fof(f140,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f105,f70])).

fof(f70,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f116,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f50,f113])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
            | ~ m1_pre_topc(X1,sK0)
            | ~ v1_tsep_1(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
            | ( m1_pre_topc(X1,sK0)
              & v1_tsep_1(X1,sK0) ) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
          | ~ m1_pre_topc(X1,sK0)
          | ~ v1_tsep_1(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
          | ( m1_pre_topc(X1,sK0)
            & v1_tsep_1(X1,sK0) ) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f111,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f51,f108])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f52,f103])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f54,f86])).

fof(f54,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f55,f90,f82])).

fof(f55,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f57,f90,f86,f82])).

fof(f57,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (7288)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (7290)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (7291)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (7292)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (7308)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (7296)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (7298)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (7312)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (7300)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (7293)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (7306)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (7299)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (7311)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (7310)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (7303)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (7302)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (7307)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (7289)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (7294)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (7287)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.44/0.54  % (7297)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.44/0.54  % (7304)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.44/0.55  % (7309)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.44/0.55  % (7301)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.44/0.55  % (7295)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.44/0.56  % (7300)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.53/0.56  fof(f968,plain,(
% 1.53/0.56    $false),
% 1.53/0.56    inference(avatar_sat_refutation,[],[f93,f95,f96,f106,f111,f116,f145,f163,f183,f203,f208,f306,f327,f466,f469,f515,f526,f555,f570,f575,f600,f601,f769,f840,f883,f937,f967])).
% 1.53/0.56  fof(f967,plain,(
% 1.53/0.56    ~spl4_3 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17 | spl4_30 | ~spl4_34),
% 1.53/0.56    inference(avatar_contradiction_clause,[],[f966])).
% 1.53/0.56  fof(f966,plain,(
% 1.53/0.56    $false | (~spl4_3 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17 | spl4_30 | ~spl4_34)),
% 1.53/0.56    inference(subsumption_resolution,[],[f965,f91])).
% 1.53/0.56  fof(f91,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~spl4_3),
% 1.53/0.56    inference(avatar_component_clause,[],[f90])).
% 1.53/0.56  fof(f90,plain,(
% 1.53/0.56    spl4_3 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.53/0.56  fof(f965,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | (~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17 | spl4_30 | ~spl4_34)),
% 1.53/0.56    inference(forward_demodulation,[],[f964,f326])).
% 1.53/0.56  fof(f326,plain,(
% 1.53/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl4_34),
% 1.53/0.56    inference(avatar_component_clause,[],[f324])).
% 1.53/0.56  fof(f324,plain,(
% 1.53/0.56    spl4_34 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.53/0.56  fof(f964,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17 | spl4_30)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f115,f110,f105,f182,f300,f74])).
% 1.53/0.56  fof(f74,plain,(
% 1.53/0.56    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f49])).
% 1.53/0.56  % (7305)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.53/0.56  fof(f49,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(nnf_transformation,[],[f32])).
% 1.53/0.56  fof(f32,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f31])).
% 1.53/0.56  fof(f31,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f8])).
% 1.53/0.56  fof(f8,axiom,(
% 1.53/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).
% 1.53/0.56  fof(f300,plain,(
% 1.53/0.56    ~v3_pre_topc(u1_struct_0(sK1),sK0) | spl4_30),
% 1.53/0.56    inference(avatar_component_clause,[],[f299])).
% 1.53/0.56  fof(f299,plain,(
% 1.53/0.56    spl4_30 <=> v3_pre_topc(u1_struct_0(sK1),sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.53/0.56  fof(f182,plain,(
% 1.53/0.56    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_17),
% 1.53/0.56    inference(avatar_component_clause,[],[f180])).
% 1.53/0.56  fof(f180,plain,(
% 1.53/0.56    spl4_17 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.53/0.56  fof(f105,plain,(
% 1.53/0.56    l1_pre_topc(sK0) | ~spl4_5),
% 1.53/0.56    inference(avatar_component_clause,[],[f103])).
% 1.53/0.56  fof(f103,plain,(
% 1.53/0.56    spl4_5 <=> l1_pre_topc(sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.53/0.56  fof(f110,plain,(
% 1.53/0.56    v2_pre_topc(sK0) | ~spl4_6),
% 1.53/0.56    inference(avatar_component_clause,[],[f108])).
% 1.53/0.56  fof(f108,plain,(
% 1.53/0.56    spl4_6 <=> v2_pre_topc(sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.53/0.56  fof(f115,plain,(
% 1.53/0.56    ~v2_struct_0(sK0) | spl4_7),
% 1.53/0.56    inference(avatar_component_clause,[],[f113])).
% 1.53/0.56  fof(f113,plain,(
% 1.53/0.56    spl4_7 <=> v2_struct_0(sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.53/0.56  fof(f937,plain,(
% 1.53/0.56    ~spl4_30 | spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_14),
% 1.53/0.56    inference(avatar_split_clause,[],[f936,f160,f103,f86,f82,f299])).
% 1.53/0.56  fof(f82,plain,(
% 1.53/0.56    spl4_1 <=> v1_tsep_1(sK1,sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.53/0.56  fof(f86,plain,(
% 1.53/0.56    spl4_2 <=> m1_pre_topc(sK1,sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.53/0.56  fof(f160,plain,(
% 1.53/0.56    spl4_14 <=> u1_struct_0(sK1) = sK3(sK0,sK1)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.53/0.56  fof(f936,plain,(
% 1.53/0.56    ~v3_pre_topc(u1_struct_0(sK1),sK0) | (spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_14)),
% 1.53/0.56    inference(subsumption_resolution,[],[f935,f105])).
% 1.53/0.56  fof(f935,plain,(
% 1.53/0.56    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | (spl4_1 | ~spl4_2 | ~spl4_14)),
% 1.53/0.56    inference(subsumption_resolution,[],[f934,f87])).
% 1.53/0.56  fof(f87,plain,(
% 1.53/0.56    m1_pre_topc(sK1,sK0) | ~spl4_2),
% 1.53/0.56    inference(avatar_component_clause,[],[f86])).
% 1.53/0.56  fof(f934,plain,(
% 1.53/0.56    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl4_1 | ~spl4_14)),
% 1.53/0.56    inference(subsumption_resolution,[],[f603,f84])).
% 1.53/0.56  fof(f84,plain,(
% 1.53/0.56    ~v1_tsep_1(sK1,sK0) | spl4_1),
% 1.53/0.56    inference(avatar_component_clause,[],[f82])).
% 1.53/0.56  fof(f603,plain,(
% 1.53/0.56    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl4_14),
% 1.53/0.56    inference(superposition,[],[f68,f162])).
% 1.53/0.56  fof(f162,plain,(
% 1.53/0.56    u1_struct_0(sK1) = sK3(sK0,sK1) | ~spl4_14),
% 1.53/0.56    inference(avatar_component_clause,[],[f160])).
% 1.53/0.56  fof(f68,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~v3_pre_topc(sK3(X0,X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f48])).
% 1.53/0.56  fof(f48,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK3(X0,X1),X0) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 1.53/0.56  fof(f47,plain,(
% 1.53/0.56    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0,X1),X0) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f46,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(rectify,[],[f45])).
% 1.53/0.56  fof(f45,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(nnf_transformation,[],[f24])).
% 1.53/0.56  fof(f24,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f23])).
% 1.53/0.56  fof(f23,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f7])).
% 1.53/0.56  fof(f7,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).
% 1.53/0.56  fof(f883,plain,(
% 1.53/0.56    spl4_3 | ~spl4_34 | ~spl4_59),
% 1.53/0.56    inference(avatar_split_clause,[],[f860,f512,f324,f90])).
% 1.53/0.56  fof(f512,plain,(
% 1.53/0.56    spl4_59 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.53/0.56  fof(f860,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (~spl4_34 | ~spl4_59)),
% 1.53/0.56    inference(backward_demodulation,[],[f514,f326])).
% 1.53/0.56  fof(f514,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl4_59),
% 1.53/0.56    inference(avatar_component_clause,[],[f512])).
% 1.53/0.56  fof(f840,plain,(
% 1.53/0.56    spl4_34 | ~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62 | ~spl4_65 | ~spl4_66 | ~spl4_86),
% 1.53/0.56    inference(avatar_split_clause,[],[f839,f766,f572,f567,f552,f113,f108,f103,f86,f324])).
% 1.53/0.56  fof(f552,plain,(
% 1.53/0.56    spl4_62 <=> v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 1.53/0.56  fof(f567,plain,(
% 1.53/0.56    spl4_65 <=> l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.53/0.56  fof(f572,plain,(
% 1.53/0.56    spl4_66 <=> v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.53/0.56  fof(f766,plain,(
% 1.53/0.56    spl4_86 <=> u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 1.53/0.56  fof(f839,plain,(
% 1.53/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62 | ~spl4_65 | ~spl4_66 | ~spl4_86)),
% 1.53/0.56    inference(trivial_inequality_removal,[],[f838])).
% 1.53/0.56  fof(f838,plain,(
% 1.53/0.56    k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,u1_struct_0(sK1)) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62 | ~spl4_65 | ~spl4_66 | ~spl4_86)),
% 1.53/0.56    inference(forward_demodulation,[],[f837,f768])).
% 1.53/0.56  fof(f768,plain,(
% 1.53/0.56    u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl4_86),
% 1.53/0.56    inference(avatar_component_clause,[],[f766])).
% 1.53/0.56  fof(f837,plain,(
% 1.53/0.56    k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62 | ~spl4_65 | ~spl4_66)),
% 1.53/0.56    inference(subsumption_resolution,[],[f836,f569])).
% 1.53/0.56  fof(f569,plain,(
% 1.53/0.56    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl4_65),
% 1.53/0.56    inference(avatar_component_clause,[],[f567])).
% 1.53/0.56  fof(f836,plain,(
% 1.53/0.56    ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62 | ~spl4_66)),
% 1.53/0.56    inference(subsumption_resolution,[],[f826,f574])).
% 1.53/0.56  fof(f574,plain,(
% 1.53/0.56    v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl4_66),
% 1.53/0.56    inference(avatar_component_clause,[],[f572])).
% 1.53/0.56  fof(f826,plain,(
% 1.53/0.56    ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62)),
% 1.53/0.56    inference(resolution,[],[f262,f554])).
% 1.53/0.56  fof(f554,plain,(
% 1.53/0.56    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl4_62),
% 1.53/0.56    inference(avatar_component_clause,[],[f552])).
% 1.53/0.56  fof(f262,plain,(
% 1.53/0.56    ( ! [X7] : (~v1_pre_topc(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | k6_tmap_1(sK0,sK2(sK0,sK1,X7)) != X7 | k8_tmap_1(sK0,sK1) = X7) ) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7)),
% 1.53/0.56    inference(resolution,[],[f155,f87])).
% 1.53/0.56  fof(f155,plain,(
% 1.53/0.56    ( ! [X4,X3] : (~v1_pre_topc(X4) | ~m1_pre_topc(X3,sK0) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | k6_tmap_1(sK0,sK2(sK0,X3,X4)) != X4 | k8_tmap_1(sK0,X3) = X4) ) | (~spl4_5 | ~spl4_6 | spl4_7)),
% 1.53/0.56    inference(subsumption_resolution,[],[f154,f110])).
% 1.53/0.56  fof(f154,plain,(
% 1.53/0.56    ( ! [X4,X3] : (k6_tmap_1(sK0,sK2(sK0,X3,X4)) != X4 | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~v1_pre_topc(X4) | ~m1_pre_topc(X3,sK0) | ~v2_pre_topc(sK0) | k8_tmap_1(sK0,X3) = X4) ) | (~spl4_5 | spl4_7)),
% 1.53/0.56    inference(subsumption_resolution,[],[f148,f105])).
% 1.53/0.56  fof(f148,plain,(
% 1.53/0.56    ( ! [X4,X3] : (k6_tmap_1(sK0,sK2(sK0,X3,X4)) != X4 | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~v1_pre_topc(X4) | ~m1_pre_topc(X3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k8_tmap_1(sK0,X3) = X4) ) | spl4_7),
% 1.53/0.56    inference(resolution,[],[f115,f61])).
% 1.53/0.56  fof(f61,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k8_tmap_1(X0,X1) = X2) )),
% 1.53/0.56    inference(cnf_transformation,[],[f43])).
% 1.53/0.56  fof(f43,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 1.53/0.56  fof(f42,plain,(
% 1.53/0.56    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f41,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(rectify,[],[f40])).
% 1.53/0.56  fof(f40,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(nnf_transformation,[],[f20])).
% 1.53/0.56  fof(f20,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f19])).
% 1.53/0.56  fof(f19,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f6])).
% 1.53/0.56  fof(f6,axiom,(
% 1.53/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).
% 1.53/0.56  fof(f769,plain,(
% 1.53/0.56    spl4_34 | spl4_86 | ~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62 | ~spl4_65 | ~spl4_66),
% 1.53/0.56    inference(avatar_split_clause,[],[f764,f572,f567,f552,f113,f108,f103,f86,f766,f324])).
% 1.53/0.56  fof(f764,plain,(
% 1.53/0.56    u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62 | ~spl4_65 | ~spl4_66)),
% 1.53/0.56    inference(subsumption_resolution,[],[f763,f569])).
% 1.53/0.56  fof(f763,plain,(
% 1.53/0.56    ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62 | ~spl4_66)),
% 1.53/0.56    inference(subsumption_resolution,[],[f751,f574])).
% 1.53/0.56  fof(f751,plain,(
% 1.53/0.56    ~v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | u1_struct_0(sK1) = sK2(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_62)),
% 1.53/0.56    inference(resolution,[],[f232,f554])).
% 1.53/0.56  fof(f232,plain,(
% 1.53/0.56    ( ! [X7] : (~v1_pre_topc(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | u1_struct_0(sK1) = sK2(sK0,sK1,X7) | k8_tmap_1(sK0,sK1) = X7) ) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7)),
% 1.53/0.56    inference(resolution,[],[f153,f87])).
% 1.53/0.56  fof(f153,plain,(
% 1.53/0.56    ( ! [X2,X1] : (~v1_pre_topc(X2) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | u1_struct_0(X1) = sK2(sK0,X1,X2) | k8_tmap_1(sK0,X1) = X2) ) | (~spl4_5 | ~spl4_6 | spl4_7)),
% 1.53/0.56    inference(subsumption_resolution,[],[f152,f110])).
% 1.53/0.56  fof(f152,plain,(
% 1.53/0.56    ( ! [X2,X1] : (u1_struct_0(X1) = sK2(sK0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(sK0) | k8_tmap_1(sK0,X1) = X2) ) | (~spl4_5 | spl4_7)),
% 1.53/0.56    inference(subsumption_resolution,[],[f147,f105])).
% 1.53/0.56  fof(f147,plain,(
% 1.53/0.56    ( ! [X2,X1] : (u1_struct_0(X1) = sK2(sK0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k8_tmap_1(sK0,X1) = X2) ) | spl4_7),
% 1.53/0.56    inference(resolution,[],[f115,f60])).
% 1.53/0.56  fof(f60,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | u1_struct_0(X1) = sK2(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k8_tmap_1(X0,X1) = X2) )),
% 1.53/0.56    inference(cnf_transformation,[],[f43])).
% 1.53/0.56  fof(f601,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.56  fof(f600,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.56  fof(f575,plain,(
% 1.53/0.56    spl4_66 | ~spl4_36 | ~spl4_59),
% 1.53/0.56    inference(avatar_split_clause,[],[f534,f512,f337,f572])).
% 1.53/0.56  fof(f337,plain,(
% 1.53/0.56    spl4_36 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.53/0.56  fof(f534,plain,(
% 1.53/0.56    v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl4_36 | ~spl4_59)),
% 1.53/0.56    inference(backward_demodulation,[],[f338,f514])).
% 1.53/0.56  fof(f338,plain,(
% 1.53/0.56    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_36),
% 1.53/0.56    inference(avatar_component_clause,[],[f337])).
% 1.53/0.56  fof(f570,plain,(
% 1.53/0.56    spl4_65 | ~spl4_35 | ~spl4_59),
% 1.53/0.56    inference(avatar_split_clause,[],[f533,f512,f333,f567])).
% 1.53/0.56  fof(f333,plain,(
% 1.53/0.56    spl4_35 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.53/0.56  fof(f533,plain,(
% 1.53/0.56    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl4_35 | ~spl4_59)),
% 1.53/0.56    inference(backward_demodulation,[],[f334,f514])).
% 1.53/0.56  fof(f334,plain,(
% 1.53/0.56    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_35),
% 1.53/0.56    inference(avatar_component_clause,[],[f333])).
% 1.53/0.56  fof(f555,plain,(
% 1.53/0.56    spl4_62 | ~spl4_19 | ~spl4_59),
% 1.53/0.56    inference(avatar_split_clause,[],[f530,f512,f205,f552])).
% 1.53/0.56  fof(f205,plain,(
% 1.53/0.56    spl4_19 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.53/0.56  fof(f530,plain,(
% 1.53/0.56    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl4_19 | ~spl4_59)),
% 1.53/0.56    inference(backward_demodulation,[],[f207,f514])).
% 1.53/0.56  fof(f207,plain,(
% 1.53/0.56    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_19),
% 1.53/0.56    inference(avatar_component_clause,[],[f205])).
% 1.53/0.56  fof(f526,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.56  fof(f515,plain,(
% 1.53/0.56    spl4_59 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17 | ~spl4_30),
% 1.53/0.56    inference(avatar_split_clause,[],[f510,f299,f180,f113,f108,f103,f512])).
% 1.53/0.56  fof(f510,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17 | ~spl4_30)),
% 1.53/0.56    inference(subsumption_resolution,[],[f505,f301])).
% 1.53/0.56  fof(f301,plain,(
% 1.53/0.56    v3_pre_topc(u1_struct_0(sK1),sK0) | ~spl4_30),
% 1.53/0.56    inference(avatar_component_clause,[],[f299])).
% 1.53/0.56  fof(f505,plain,(
% 1.53/0.56    ~v3_pre_topc(u1_struct_0(sK1),sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17)),
% 1.53/0.56    inference(resolution,[],[f150,f182])).
% 1.53/0.56  fof(f150,plain,(
% 1.53/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X0)) ) | (~spl4_5 | ~spl4_6 | spl4_7)),
% 1.53/0.56    inference(subsumption_resolution,[],[f149,f110])).
% 1.53/0.56  fof(f149,plain,(
% 1.53/0.56    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X0)) ) | (~spl4_5 | spl4_7)),
% 1.53/0.56    inference(subsumption_resolution,[],[f146,f105])).
% 1.53/0.56  fof(f146,plain,(
% 1.53/0.56    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X0)) ) | spl4_7),
% 1.53/0.56    inference(resolution,[],[f115,f73])).
% 1.53/0.56  fof(f73,plain,(
% 1.53/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f49])).
% 1.53/0.56  fof(f469,plain,(
% 1.53/0.56    spl4_35 | ~spl4_5 | ~spl4_18),
% 1.53/0.56    inference(avatar_split_clause,[],[f443,f200,f103,f333])).
% 1.53/0.56  fof(f200,plain,(
% 1.53/0.56    spl4_18 <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.53/0.56  fof(f443,plain,(
% 1.53/0.56    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_5 | ~spl4_18)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f105,f202,f69])).
% 1.53/0.56  fof(f69,plain,(
% 1.53/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f25])).
% 1.53/0.56  fof(f25,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f3])).
% 1.53/0.56  fof(f3,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.53/0.56  fof(f202,plain,(
% 1.53/0.56    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) | ~spl4_18),
% 1.53/0.56    inference(avatar_component_clause,[],[f200])).
% 1.53/0.56  fof(f466,plain,(
% 1.53/0.56    spl4_36 | ~spl4_5 | ~spl4_6 | ~spl4_18),
% 1.53/0.56    inference(avatar_split_clause,[],[f445,f200,f108,f103,f337])).
% 1.53/0.56  fof(f445,plain,(
% 1.53/0.56    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_5 | ~spl4_6 | ~spl4_18)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f110,f105,f202,f72])).
% 1.53/0.56  fof(f72,plain,(
% 1.53/0.56    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f30])).
% 1.53/0.56  fof(f30,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f29])).
% 1.53/0.56  fof(f29,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f2])).
% 1.53/0.56  fof(f2,axiom,(
% 1.53/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.53/0.56  fof(f327,plain,(
% 1.53/0.56    ~spl4_31 | ~spl4_32 | ~spl4_33 | spl4_34 | ~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17),
% 1.53/0.56    inference(avatar_split_clause,[],[f310,f180,f113,f108,f103,f86,f324,f320,f316,f312])).
% 1.53/0.56  fof(f312,plain,(
% 1.53/0.56    spl4_31 <=> v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.53/0.56  fof(f316,plain,(
% 1.53/0.56    spl4_32 <=> v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.53/0.56  fof(f320,plain,(
% 1.53/0.56    spl4_33 <=> l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.53/0.56  fof(f310,plain,(
% 1.53/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_17)),
% 1.53/0.56    inference(subsumption_resolution,[],[f309,f115])).
% 1.53/0.56  fof(f309,plain,(
% 1.53/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_5 | ~spl4_6 | ~spl4_17)),
% 1.53/0.56    inference(subsumption_resolution,[],[f308,f110])).
% 1.53/0.56  fof(f308,plain,(
% 1.53/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_5 | ~spl4_17)),
% 1.53/0.56    inference(subsumption_resolution,[],[f307,f105])).
% 1.53/0.56  fof(f307,plain,(
% 1.53/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_17)),
% 1.53/0.56    inference(subsumption_resolution,[],[f297,f87])).
% 1.53/0.56  fof(f297,plain,(
% 1.53/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_17),
% 1.53/0.56    inference(resolution,[],[f182,f79])).
% 1.53/0.56  fof(f79,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.56    inference(equality_resolution,[],[f78])).
% 1.53/0.56  fof(f78,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.56    inference(equality_resolution,[],[f58])).
% 1.53/0.56  fof(f58,plain,(
% 1.53/0.56    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f43])).
% 1.53/0.56  fof(f306,plain,(
% 1.53/0.56    spl4_30 | ~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_17),
% 1.53/0.56    inference(avatar_split_clause,[],[f305,f180,f103,f86,f82,f299])).
% 1.53/0.56  fof(f305,plain,(
% 1.53/0.56    v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_17)),
% 1.53/0.56    inference(subsumption_resolution,[],[f304,f105])).
% 1.53/0.56  fof(f304,plain,(
% 1.53/0.56    v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_2 | ~spl4_17)),
% 1.53/0.56    inference(subsumption_resolution,[],[f303,f87])).
% 1.53/0.56  fof(f303,plain,(
% 1.53/0.56    v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_17)),
% 1.53/0.56    inference(subsumption_resolution,[],[f296,f83])).
% 1.53/0.56  fof(f83,plain,(
% 1.53/0.56    v1_tsep_1(sK1,sK0) | ~spl4_1),
% 1.53/0.56    inference(avatar_component_clause,[],[f82])).
% 1.53/0.56  fof(f296,plain,(
% 1.53/0.56    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl4_17),
% 1.53/0.56    inference(resolution,[],[f182,f80])).
% 1.53/0.56  fof(f80,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(equality_resolution,[],[f65])).
% 1.53/0.56  fof(f65,plain,(
% 1.53/0.56    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f48])).
% 1.53/0.56  fof(f208,plain,(
% 1.53/0.56    spl4_19 | ~spl4_5 | ~spl4_13),
% 1.53/0.56    inference(avatar_split_clause,[],[f197,f142,f103,f205])).
% 1.53/0.56  fof(f142,plain,(
% 1.53/0.56    spl4_13 <=> m1_pre_topc(sK0,sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.53/0.56  fof(f197,plain,(
% 1.53/0.56    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_5 | ~spl4_13)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f105,f144,f76])).
% 1.53/0.56  fof(f76,plain,(
% 1.53/0.56    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f34])).
% 1.53/0.56  fof(f34,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f9])).
% 1.53/0.56  fof(f9,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.53/0.56  fof(f144,plain,(
% 1.53/0.56    m1_pre_topc(sK0,sK0) | ~spl4_13),
% 1.53/0.56    inference(avatar_component_clause,[],[f142])).
% 1.53/0.56  fof(f203,plain,(
% 1.53/0.56    spl4_18 | ~spl4_5 | ~spl4_13),
% 1.53/0.56    inference(avatar_split_clause,[],[f198,f142,f103,f200])).
% 1.53/0.56  fof(f198,plain,(
% 1.53/0.56    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) | (~spl4_5 | ~spl4_13)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f105,f144,f77])).
% 1.53/0.56  fof(f77,plain,(
% 1.53/0.56    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f34])).
% 1.53/0.56  fof(f183,plain,(
% 1.53/0.56    spl4_17 | ~spl4_2 | ~spl4_5),
% 1.53/0.56    inference(avatar_split_clause,[],[f166,f103,f86,f180])).
% 1.53/0.56  fof(f166,plain,(
% 1.53/0.56    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_5)),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f105,f87,f75])).
% 1.53/0.56  fof(f75,plain,(
% 1.53/0.56    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f33])).
% 1.53/0.56  fof(f33,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f10])).
% 1.53/0.56  fof(f10,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.53/0.56  fof(f163,plain,(
% 1.53/0.56    spl4_14 | spl4_1 | ~spl4_2 | ~spl4_5),
% 1.53/0.56    inference(avatar_split_clause,[],[f158,f103,f86,f82,f160])).
% 1.53/0.56  fof(f158,plain,(
% 1.53/0.56    u1_struct_0(sK1) = sK3(sK0,sK1) | (spl4_1 | ~spl4_2 | ~spl4_5)),
% 1.53/0.56    inference(subsumption_resolution,[],[f157,f105])).
% 1.53/0.56  fof(f157,plain,(
% 1.53/0.56    u1_struct_0(sK1) = sK3(sK0,sK1) | ~l1_pre_topc(sK0) | (spl4_1 | ~spl4_2)),
% 1.53/0.56    inference(subsumption_resolution,[],[f156,f87])).
% 1.53/0.56  fof(f156,plain,(
% 1.53/0.56    u1_struct_0(sK1) = sK3(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl4_1),
% 1.53/0.56    inference(resolution,[],[f84,f67])).
% 1.53/0.56  fof(f67,plain,(
% 1.53/0.56    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f48])).
% 1.53/0.56  fof(f145,plain,(
% 1.53/0.56    spl4_13 | ~spl4_5),
% 1.53/0.56    inference(avatar_split_clause,[],[f140,f103,f142])).
% 1.53/0.56  fof(f140,plain,(
% 1.53/0.56    m1_pre_topc(sK0,sK0) | ~spl4_5),
% 1.53/0.56    inference(unit_resulting_resolution,[],[f105,f70])).
% 1.53/0.56  fof(f70,plain,(
% 1.53/0.56    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f26])).
% 1.53/0.56  fof(f26,plain,(
% 1.53/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f11])).
% 1.53/0.56  fof(f11,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.53/0.56  fof(f116,plain,(
% 1.53/0.56    ~spl4_7),
% 1.53/0.56    inference(avatar_split_clause,[],[f50,f113])).
% 1.53/0.56  fof(f50,plain,(
% 1.53/0.56    ~v2_struct_0(sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f39])).
% 1.53/0.56  fof(f39,plain,(
% 1.53/0.56    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 1.53/0.56  fof(f37,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f38,plain,(
% 1.53/0.56    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f36,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f35])).
% 1.53/0.56  fof(f35,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.56    inference(nnf_transformation,[],[f18])).
% 1.53/0.56  fof(f18,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.56    inference(flattening,[],[f17])).
% 1.53/0.56  fof(f17,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f16])).
% 1.53/0.56  fof(f16,negated_conjecture,(
% 1.53/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 1.53/0.56    inference(negated_conjecture,[],[f15])).
% 1.53/0.56  fof(f15,conjecture,(
% 1.53/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).
% 1.53/0.56  fof(f111,plain,(
% 1.53/0.56    spl4_6),
% 1.53/0.56    inference(avatar_split_clause,[],[f51,f108])).
% 1.53/0.56  fof(f51,plain,(
% 1.53/0.56    v2_pre_topc(sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f39])).
% 1.53/0.56  fof(f106,plain,(
% 1.53/0.56    spl4_5),
% 1.53/0.56    inference(avatar_split_clause,[],[f52,f103])).
% 1.53/0.56  fof(f52,plain,(
% 1.53/0.56    l1_pre_topc(sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f39])).
% 1.53/0.56  fof(f96,plain,(
% 1.53/0.56    spl4_2),
% 1.53/0.56    inference(avatar_split_clause,[],[f54,f86])).
% 1.53/0.56  fof(f54,plain,(
% 1.53/0.56    m1_pre_topc(sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f39])).
% 1.53/0.56  fof(f95,plain,(
% 1.53/0.56    spl4_1 | spl4_3),
% 1.53/0.56    inference(avatar_split_clause,[],[f55,f90,f82])).
% 1.53/0.56  fof(f55,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f39])).
% 1.53/0.56  fof(f93,plain,(
% 1.53/0.56    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.53/0.56    inference(avatar_split_clause,[],[f57,f90,f86,f82])).
% 1.53/0.56  fof(f57,plain,(
% 1.53/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f39])).
% 1.53/0.56  % SZS output end Proof for theBenchmark
% 1.53/0.56  % (7300)------------------------------
% 1.53/0.56  % (7300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (7300)Termination reason: Refutation
% 1.53/0.56  
% 1.53/0.56  % (7300)Memory used [KB]: 6908
% 1.53/0.56  % (7300)Time elapsed: 0.152 s
% 1.53/0.56  % (7300)------------------------------
% 1.53/0.56  % (7300)------------------------------
% 1.53/0.56  % (7286)Success in time 0.2 s
%------------------------------------------------------------------------------
