%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 537 expanded)
%              Number of leaves         :   50 ( 207 expanded)
%              Depth                    :   13
%              Number of atoms          : 1006 (2362 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f125,f130,f135,f140,f149,f151,f199,f296,f328,f339,f343,f361,f375,f381,f411,f451,f468,f484,f537,f553,f572,f577,f582,f755,f1321,f1331,f1342])).

fof(f1342,plain,
    ( ~ spl4_43
    | spl4_55 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | ~ spl4_43
    | spl4_55 ),
    inference(subsumption_resolution,[],[f1339,f581])).

fof(f581,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl4_43
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f1339,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl4_55 ),
    inference(resolution,[],[f754,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f754,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f752])).

fof(f752,plain,
    ( spl4_55
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f1331,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_88 ),
    inference(avatar_contradiction_clause,[],[f1330])).

fof(f1330,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1329,f114])).

fof(f114,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1329,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1328,f119])).

fof(f119,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1328,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1327,f129])).

fof(f129,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1327,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1326,f134])).

fof(f134,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1326,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1325,f139])).

fof(f139,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1325,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1323,f144])).

fof(f144,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_7
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1323,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_88 ),
    inference(resolution,[],[f1320,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f1320,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1318,plain,
    ( spl4_88
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1321,plain,
    ( spl4_88
    | ~ spl4_24
    | ~ spl4_41
    | ~ spl4_43
    | spl4_54 ),
    inference(avatar_split_clause,[],[f1316,f748,f579,f569,f325,f1318])).

fof(f325,plain,
    ( spl4_24
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f569,plain,
    ( spl4_41
  <=> v2_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f748,plain,
    ( spl4_54
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1316,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ spl4_24
    | ~ spl4_41
    | ~ spl4_43
    | spl4_54 ),
    inference(subsumption_resolution,[],[f1315,f581])).

fof(f1315,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_24
    | ~ spl4_41
    | spl4_54 ),
    inference(subsumption_resolution,[],[f1314,f750])).

fof(f750,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | spl4_54 ),
    inference(avatar_component_clause,[],[f748])).

fof(f1314,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_24
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f479,f571])).

fof(f571,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f569])).

fof(f479,plain,
    ( ~ v2_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_24 ),
    inference(resolution,[],[f327,f202])).

fof(f202,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f82,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f82,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f327,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f325])).

fof(f755,plain,
    ( ~ spl4_54
    | ~ spl4_55
    | spl4_8
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f585,f574,f146,f752,f748])).

fof(f146,plain,
    ( spl4_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f574,plain,
    ( spl4_42
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f585,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | spl4_8
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f584,f147])).

fof(f147,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f584,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ spl4_42 ),
    inference(superposition,[],[f93,f576])).

fof(f576,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f574])).

fof(f93,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f582,plain,
    ( spl4_43
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f567,f481,f127,f579])).

fof(f481,plain,
    ( spl4_37
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f567,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f563,f129])).

fof(f563,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_37 ),
    inference(resolution,[],[f483,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f483,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f481])).

fof(f577,plain,
    ( spl4_42
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f559,f359,f142,f137,f132,f574])).

fof(f359,plain,
    ( spl4_28
  <=> ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f559,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f558,f134])).

fof(f558,plain,
    ( v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f554,f139])).

fof(f554,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl4_7
    | ~ spl4_28 ),
    inference(resolution,[],[f144,f360])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | u1_struct_0(sK2(sK0,X0)) = X0 )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f359])).

fof(f572,plain,
    ( spl4_41
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f566,f481,f127,f122,f112,f569])).

fof(f122,plain,
    ( spl4_3
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f566,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f565,f114])).

fof(f565,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f564,f124])).

fof(f124,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f564,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f562,f129])).

fof(f562,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_37 ),
    inference(resolution,[],[f483,f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f553,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_7
    | ~ spl4_34
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_7
    | ~ spl4_34
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f551,f114])).

fof(f551,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_7
    | ~ spl4_34
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f550,f119])).

fof(f550,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_7
    | ~ spl4_34
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f549,f129])).

fof(f549,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_7
    | ~ spl4_34
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f548,f450])).

fof(f450,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl4_34
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f548,plain,
    ( ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_7
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f542,f143])).

fof(f143,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f542,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_40 ),
    inference(superposition,[],[f87,f536])).

fof(f536,plain,
    ( sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl4_40
  <=> sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f537,plain,
    ( spl4_40
    | spl4_5
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f532,f465,f137,f132,f534])).

fof(f465,plain,
    ( spl4_36
  <=> sK1 = k1_tarski(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f532,plain,
    ( sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | spl4_5
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f531,f467])).

fof(f467,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f465])).

fof(f531,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f527,f134])).

fof(f527,plain,
    ( v1_xboole_0(sK1)
    | k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f248,f139])).

fof(f248,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | v1_xboole_0(X2)
      | k1_tarski(sK3(X2)) = k6_domain_1(X3,sK3(X2)) ) ),
    inference(subsumption_resolution,[],[f246,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f246,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | v1_xboole_0(X2)
      | k1_tarski(sK3(X2)) = k6_domain_1(X3,sK3(X2))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f175,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f175,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f107,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f484,plain,
    ( spl4_37
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f476,f341,f142,f137,f132,f481])).

fof(f341,plain,
    ( spl4_26
  <=> ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_pre_topc(sK2(sK0,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f476,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f475,f134])).

fof(f475,plain,
    ( v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f470,f139])).

fof(f470,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(resolution,[],[f144,f342])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_pre_topc(sK2(sK0,X0),sK0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f341])).

fof(f468,plain,
    ( spl4_36
    | ~ spl4_13
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f429,f372,f197,f465])).

fof(f197,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f372,plain,
    ( spl4_30
  <=> r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f429,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ spl4_13
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f425,f76])).

fof(f76,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f425,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | ~ spl4_13
    | ~ spl4_30 ),
    inference(resolution,[],[f374,f198])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | v1_xboole_0(X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f197])).

fof(f374,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f372])).

fof(f451,plain,
    ( spl4_34
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f418,f408,f448])).

fof(f408,plain,
    ( spl4_31
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f418,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_31 ),
    inference(resolution,[],[f410,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f97,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f410,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f408])).

fof(f411,plain,
    ( spl4_31
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f406,f137,f132,f408])).

fof(f406,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f402,f134])).

fof(f402,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f249,f139])).

fof(f249,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | v1_xboole_0(X4)
      | r2_hidden(sK3(X4),X5) ) ),
    inference(subsumption_resolution,[],[f247,f85])).

fof(f247,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | v1_xboole_0(X4)
      | r2_hidden(sK3(X4),X5)
      | v1_xboole_0(X5) ) ),
    inference(resolution,[],[f175,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f381,plain,
    ( spl4_5
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl4_5
    | spl4_29 ),
    inference(subsumption_resolution,[],[f377,f134])).

fof(f377,plain,
    ( v1_xboole_0(sK1)
    | spl4_29 ),
    inference(resolution,[],[f370,f163])).

fof(f163,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f162,f95])).

fof(f370,plain,
    ( ~ m1_subset_1(sK3(sK1),sK1)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl4_29
  <=> m1_subset_1(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f375,plain,
    ( ~ spl4_29
    | spl4_30
    | spl4_5
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f348,f336,f132,f372,f368])).

fof(f336,plain,
    ( spl4_25
  <=> k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f348,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ m1_subset_1(sK3(sK1),sK1)
    | spl4_5
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f345,f134])).

fof(f345,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3(sK1),sK1)
    | ~ spl4_25 ),
    inference(superposition,[],[f190,f338])).

fof(f338,plain,
    ( k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f336])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f101,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f361,plain,
    ( spl4_28
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f244,f127,f117,f112,f359])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | u1_struct_0(sK2(sK0,X0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f243,f114])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | u1_struct_0(sK2(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f242,f119])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | u1_struct_0(sK2(sK0,X0)) = X0
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f129])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f343,plain,
    ( spl4_26
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f239,f127,f117,f112,f341])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_pre_topc(sK2(sK0,X0),sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f238,f114])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_pre_topc(sK2(sK0,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f237,f119])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_pre_topc(sK2(sK0,X0),sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f91,f129])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f339,plain,
    ( spl4_25
    | spl4_5 ),
    inference(avatar_split_clause,[],[f258,f132,f336])).

fof(f258,plain,
    ( k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1))
    | spl4_5 ),
    inference(resolution,[],[f180,f134])).

fof(f180,plain,(
    ! [X2] :
      ( v1_xboole_0(X2)
      | k6_domain_1(X2,sK3(X2)) = k1_tarski(sK3(X2)) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X2] :
      ( k6_domain_1(X2,sK3(X2)) = k1_tarski(sK3(X2))
      | v1_xboole_0(X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f100,f163])).

fof(f328,plain,
    ( spl4_24
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f315,f294,f142,f137,f132,f325])).

fof(f294,plain,
    ( spl4_22
  <=> ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_tdlat_3(sK2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f315,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f314,f134])).

fof(f314,plain,
    ( v1_xboole_0(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f312,f139])).

fof(f312,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(resolution,[],[f295,f144])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_tdlat_3(sK2(sK0,X0)) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( spl4_22
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f235,f127,f117,f112,f294])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_tdlat_3(sK2(sK0,X0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f234,f114])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_tdlat_3(sK2(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f233,f119])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_tdlat_3(sK2(sK0,X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f90,f129])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v1_tdlat_3(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f199,plain,
    ( spl4_13
    | spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f195,f146,f132,f197])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | v1_xboole_0(X0) )
    | spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f193,f134])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | v1_xboole_0(sK1)
        | v1_xboole_0(X0) )
    | ~ spl4_8 ),
    inference(resolution,[],[f77,f148])).

fof(f148,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f151,plain,
    ( ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f150,f146,f142])).

fof(f150,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f75,f148])).

fof(f75,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f149,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f74,f146,f142])).

fof(f74,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f140,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f73,f137])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f135,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f72,f132])).

fof(f72,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f130,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f71,f127])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f125,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f70,f122])).

fof(f70,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f120,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f69,f117])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f115,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f68,f112])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:06:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (2269)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.49  % (2261)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.49  % (2255)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (2256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (2273)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (2254)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (2271)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (2272)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (2263)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (2262)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (2265)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (2258)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (2264)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (2268)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (2247)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (2247)Refutation not found, incomplete strategy% (2247)------------------------------
% 0.22/0.54  % (2247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2247)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2247)Memory used [KB]: 10618
% 0.22/0.54  % (2247)Time elapsed: 0.125 s
% 0.22/0.54  % (2247)------------------------------
% 0.22/0.54  % (2247)------------------------------
% 0.22/0.54  % (2259)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (2270)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (2266)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (2252)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (2274)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (2277)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (2275)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (2276)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % (2257)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.56  % (2267)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.57  % (2260)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (2254)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f1343,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f115,f120,f125,f130,f135,f140,f149,f151,f199,f296,f328,f339,f343,f361,f375,f381,f411,f451,f468,f484,f537,f553,f572,f577,f582,f755,f1321,f1331,f1342])).
% 0.22/0.57  fof(f1342,plain,(
% 0.22/0.57    ~spl4_43 | spl4_55),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f1341])).
% 0.22/0.57  fof(f1341,plain,(
% 0.22/0.57    $false | (~spl4_43 | spl4_55)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1339,f581])).
% 0.22/0.57  fof(f581,plain,(
% 0.22/0.57    l1_pre_topc(sK2(sK0,sK1)) | ~spl4_43),
% 0.22/0.57    inference(avatar_component_clause,[],[f579])).
% 0.22/0.57  fof(f579,plain,(
% 0.22/0.57    spl4_43 <=> l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.22/0.57  fof(f1339,plain,(
% 0.22/0.57    ~l1_pre_topc(sK2(sK0,sK1)) | spl4_55),
% 0.22/0.57    inference(resolution,[],[f754,f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.57  fof(f754,plain,(
% 0.22/0.57    ~l1_struct_0(sK2(sK0,sK1)) | spl4_55),
% 0.22/0.57    inference(avatar_component_clause,[],[f752])).
% 0.22/0.57  fof(f752,plain,(
% 0.22/0.57    spl4_55 <=> l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.22/0.57  fof(f1331,plain,(
% 0.22/0.57    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_88),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f1330])).
% 0.22/0.57  fof(f1330,plain,(
% 0.22/0.57    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_88)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1329,f114])).
% 0.22/0.57  fof(f114,plain,(
% 0.22/0.57    ~v2_struct_0(sK0) | spl4_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f112])).
% 0.22/0.57  fof(f112,plain,(
% 0.22/0.57    spl4_1 <=> v2_struct_0(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.57  fof(f1329,plain,(
% 0.22/0.57    v2_struct_0(sK0) | (~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_88)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1328,f119])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    v2_pre_topc(sK0) | ~spl4_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f117])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    spl4_2 <=> v2_pre_topc(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.57  fof(f1328,plain,(
% 0.22/0.57    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_88)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1327,f129])).
% 0.22/0.57  fof(f129,plain,(
% 0.22/0.57    l1_pre_topc(sK0) | ~spl4_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f127])).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    spl4_4 <=> l1_pre_topc(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.57  fof(f1327,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_88)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1326,f134])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ~v1_xboole_0(sK1) | spl4_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f132])).
% 0.22/0.57  fof(f132,plain,(
% 0.22/0.57    spl4_5 <=> v1_xboole_0(sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.57  fof(f1326,plain,(
% 0.22/0.57    v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_6 | ~spl4_7 | ~spl4_88)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1325,f139])).
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f137])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.57  fof(f1325,plain,(
% 0.22/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_7 | ~spl4_88)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1323,f144])).
% 0.22/0.57  fof(f144,plain,(
% 0.22/0.57    v2_tex_2(sK1,sK0) | ~spl4_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f142])).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    spl4_7 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.57  fof(f1323,plain,(
% 0.22/0.57    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_88),
% 0.22/0.57    inference(resolution,[],[f1320,f88])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.22/0.57  fof(f1320,plain,(
% 0.22/0.57    v2_struct_0(sK2(sK0,sK1)) | ~spl4_88),
% 0.22/0.57    inference(avatar_component_clause,[],[f1318])).
% 0.22/0.57  fof(f1318,plain,(
% 0.22/0.57    spl4_88 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 0.22/0.57  fof(f1321,plain,(
% 0.22/0.57    spl4_88 | ~spl4_24 | ~spl4_41 | ~spl4_43 | spl4_54),
% 0.22/0.57    inference(avatar_split_clause,[],[f1316,f748,f579,f569,f325,f1318])).
% 0.22/0.57  fof(f325,plain,(
% 0.22/0.57    spl4_24 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.57  fof(f569,plain,(
% 0.22/0.57    spl4_41 <=> v2_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.22/0.57  fof(f748,plain,(
% 0.22/0.57    spl4_54 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.22/0.57  fof(f1316,plain,(
% 0.22/0.57    v2_struct_0(sK2(sK0,sK1)) | (~spl4_24 | ~spl4_41 | ~spl4_43 | spl4_54)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1315,f581])).
% 0.22/0.57  fof(f1315,plain,(
% 0.22/0.57    v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | (~spl4_24 | ~spl4_41 | spl4_54)),
% 0.22/0.57    inference(subsumption_resolution,[],[f1314,f750])).
% 0.22/0.57  fof(f750,plain,(
% 0.22/0.57    ~v7_struct_0(sK2(sK0,sK1)) | spl4_54),
% 0.22/0.57    inference(avatar_component_clause,[],[f748])).
% 0.22/0.57  fof(f1314,plain,(
% 0.22/0.57    v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | (~spl4_24 | ~spl4_41)),
% 0.22/0.57    inference(subsumption_resolution,[],[f479,f571])).
% 0.22/0.57  fof(f571,plain,(
% 0.22/0.57    v2_tdlat_3(sK2(sK0,sK1)) | ~spl4_41),
% 0.22/0.57    inference(avatar_component_clause,[],[f569])).
% 0.22/0.57  fof(f479,plain,(
% 0.22/0.57    ~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | ~spl4_24),
% 0.22/0.57    inference(resolution,[],[f327,f202])).
% 0.22/0.57  fof(f202,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_tdlat_3(X0) | ~v2_tdlat_3(X0) | v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f82,f79])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 0.22/0.57  fof(f327,plain,(
% 0.22/0.57    v1_tdlat_3(sK2(sK0,sK1)) | ~spl4_24),
% 0.22/0.57    inference(avatar_component_clause,[],[f325])).
% 0.22/0.57  fof(f755,plain,(
% 0.22/0.57    ~spl4_54 | ~spl4_55 | spl4_8 | ~spl4_42),
% 0.22/0.57    inference(avatar_split_clause,[],[f585,f574,f146,f752,f748])).
% 0.22/0.57  fof(f146,plain,(
% 0.22/0.57    spl4_8 <=> v1_zfmisc_1(sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.57  fof(f574,plain,(
% 0.22/0.57    spl4_42 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.22/0.57  fof(f585,plain,(
% 0.22/0.57    ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | (spl4_8 | ~spl4_42)),
% 0.22/0.57    inference(subsumption_resolution,[],[f584,f147])).
% 0.22/0.57  fof(f147,plain,(
% 0.22/0.57    ~v1_zfmisc_1(sK1) | spl4_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f146])).
% 0.22/0.57  fof(f584,plain,(
% 0.22/0.57    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~spl4_42),
% 0.22/0.57    inference(superposition,[],[f93,f576])).
% 0.22/0.57  fof(f576,plain,(
% 0.22/0.57    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl4_42),
% 0.22/0.57    inference(avatar_component_clause,[],[f574])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.57  fof(f582,plain,(
% 0.22/0.57    spl4_43 | ~spl4_4 | ~spl4_37),
% 0.22/0.57    inference(avatar_split_clause,[],[f567,f481,f127,f579])).
% 0.22/0.57  fof(f481,plain,(
% 0.22/0.57    spl4_37 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.57  fof(f567,plain,(
% 0.22/0.57    l1_pre_topc(sK2(sK0,sK1)) | (~spl4_4 | ~spl4_37)),
% 0.22/0.57    inference(subsumption_resolution,[],[f563,f129])).
% 0.22/0.57  fof(f563,plain,(
% 0.22/0.57    l1_pre_topc(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl4_37),
% 0.22/0.57    inference(resolution,[],[f483,f84])).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.57  fof(f483,plain,(
% 0.22/0.57    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl4_37),
% 0.22/0.57    inference(avatar_component_clause,[],[f481])).
% 0.22/0.57  fof(f577,plain,(
% 0.22/0.57    spl4_42 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_28),
% 0.22/0.57    inference(avatar_split_clause,[],[f559,f359,f142,f137,f132,f574])).
% 0.22/0.57  fof(f359,plain,(
% 0.22/0.57    spl4_28 <=> ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.57  fof(f559,plain,(
% 0.22/0.57    sK1 = u1_struct_0(sK2(sK0,sK1)) | (spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_28)),
% 0.22/0.57    inference(subsumption_resolution,[],[f558,f134])).
% 0.22/0.57  fof(f558,plain,(
% 0.22/0.57    v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1)) | (~spl4_6 | ~spl4_7 | ~spl4_28)),
% 0.22/0.57    inference(subsumption_resolution,[],[f554,f139])).
% 0.22/0.57  fof(f554,plain,(
% 0.22/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1)) | (~spl4_7 | ~spl4_28)),
% 0.22/0.57    inference(resolution,[],[f144,f360])).
% 0.22/0.57  fof(f360,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0) ) | ~spl4_28),
% 0.22/0.57    inference(avatar_component_clause,[],[f359])).
% 0.22/0.57  fof(f572,plain,(
% 0.22/0.57    spl4_41 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_37),
% 0.22/0.57    inference(avatar_split_clause,[],[f566,f481,f127,f122,f112,f569])).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    spl4_3 <=> v2_tdlat_3(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.57  fof(f566,plain,(
% 0.22/0.57    v2_tdlat_3(sK2(sK0,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_37)),
% 0.22/0.57    inference(subsumption_resolution,[],[f565,f114])).
% 0.22/0.57  fof(f565,plain,(
% 0.22/0.57    v2_tdlat_3(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_4 | ~spl4_37)),
% 0.22/0.57    inference(subsumption_resolution,[],[f564,f124])).
% 0.22/0.57  fof(f124,plain,(
% 0.22/0.57    v2_tdlat_3(sK0) | ~spl4_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f122])).
% 0.22/0.57  fof(f564,plain,(
% 0.22/0.57    v2_tdlat_3(sK2(sK0,sK1)) | ~v2_tdlat_3(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_37)),
% 0.22/0.57    inference(subsumption_resolution,[],[f562,f129])).
% 0.22/0.57  fof(f562,plain,(
% 0.22/0.57    v2_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | v2_struct_0(sK0) | ~spl4_37),
% 0.22/0.57    inference(resolution,[],[f483,f218])).
% 0.22/0.57  fof(f218,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f86,f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 0.22/0.57  fof(f553,plain,(
% 0.22/0.57    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_7 | ~spl4_34 | ~spl4_40),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f552])).
% 0.22/0.57  fof(f552,plain,(
% 0.22/0.57    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_7 | ~spl4_34 | ~spl4_40)),
% 0.22/0.57    inference(subsumption_resolution,[],[f551,f114])).
% 0.22/0.57  fof(f551,plain,(
% 0.22/0.57    v2_struct_0(sK0) | (~spl4_2 | ~spl4_4 | spl4_7 | ~spl4_34 | ~spl4_40)),
% 0.22/0.57    inference(subsumption_resolution,[],[f550,f119])).
% 0.22/0.57  fof(f550,plain,(
% 0.22/0.57    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_4 | spl4_7 | ~spl4_34 | ~spl4_40)),
% 0.22/0.57    inference(subsumption_resolution,[],[f549,f129])).
% 0.22/0.57  fof(f549,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_7 | ~spl4_34 | ~spl4_40)),
% 0.22/0.57    inference(subsumption_resolution,[],[f548,f450])).
% 0.22/0.57  fof(f450,plain,(
% 0.22/0.57    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl4_34),
% 0.22/0.57    inference(avatar_component_clause,[],[f448])).
% 0.22/0.57  fof(f448,plain,(
% 0.22/0.57    spl4_34 <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.57  fof(f548,plain,(
% 0.22/0.57    ~m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_7 | ~spl4_40)),
% 0.22/0.57    inference(subsumption_resolution,[],[f542,f143])).
% 0.22/0.57  fof(f143,plain,(
% 0.22/0.57    ~v2_tex_2(sK1,sK0) | spl4_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f142])).
% 0.22/0.57  fof(f542,plain,(
% 0.22/0.57    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_40),
% 0.22/0.57    inference(superposition,[],[f87,f536])).
% 0.22/0.57  fof(f536,plain,(
% 0.22/0.57    sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | ~spl4_40),
% 0.22/0.57    inference(avatar_component_clause,[],[f534])).
% 0.22/0.57  fof(f534,plain,(
% 0.22/0.57    spl4_40 <=> sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.57  fof(f537,plain,(
% 0.22/0.57    spl4_40 | spl4_5 | ~spl4_6 | ~spl4_36),
% 0.22/0.57    inference(avatar_split_clause,[],[f532,f465,f137,f132,f534])).
% 0.22/0.57  fof(f465,plain,(
% 0.22/0.57    spl4_36 <=> sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.57  fof(f532,plain,(
% 0.22/0.57    sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | (spl4_5 | ~spl4_6 | ~spl4_36)),
% 0.22/0.57    inference(forward_demodulation,[],[f531,f467])).
% 0.22/0.57  fof(f467,plain,(
% 0.22/0.57    sK1 = k1_tarski(sK3(sK1)) | ~spl4_36),
% 0.22/0.57    inference(avatar_component_clause,[],[f465])).
% 0.22/0.57  fof(f531,plain,(
% 0.22/0.57    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | (spl4_5 | ~spl4_6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f527,f134])).
% 0.22/0.57  fof(f527,plain,(
% 0.22/0.57    v1_xboole_0(sK1) | k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | ~spl4_6),
% 0.22/0.57    inference(resolution,[],[f248,f139])).
% 0.22/0.57  fof(f248,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | v1_xboole_0(X2) | k1_tarski(sK3(X2)) = k6_domain_1(X3,sK3(X2))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f246,f85])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.57  fof(f246,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | v1_xboole_0(X2) | k1_tarski(sK3(X2)) = k6_domain_1(X3,sK3(X2)) | v1_xboole_0(X3)) )),
% 0.22/0.57    inference(resolution,[],[f175,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.57  fof(f175,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(sK3(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(resolution,[],[f107,f95])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.57    inference(rectify,[],[f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.57    inference(flattening,[],[f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.57  fof(f484,plain,(
% 0.22/0.57    spl4_37 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_26),
% 0.22/0.57    inference(avatar_split_clause,[],[f476,f341,f142,f137,f132,f481])).
% 0.22/0.57  fof(f341,plain,(
% 0.22/0.57    spl4_26 <=> ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.57  fof(f476,plain,(
% 0.22/0.57    m1_pre_topc(sK2(sK0,sK1),sK0) | (spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_26)),
% 0.22/0.57    inference(subsumption_resolution,[],[f475,f134])).
% 0.22/0.57  fof(f475,plain,(
% 0.22/0.57    v1_xboole_0(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | (~spl4_6 | ~spl4_7 | ~spl4_26)),
% 0.22/0.57    inference(subsumption_resolution,[],[f470,f139])).
% 0.22/0.58  fof(f470,plain,(
% 0.22/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | (~spl4_7 | ~spl4_26)),
% 0.22/0.58    inference(resolution,[],[f144,f342])).
% 0.22/0.58  fof(f342,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0)) ) | ~spl4_26),
% 0.22/0.58    inference(avatar_component_clause,[],[f341])).
% 0.22/0.58  fof(f468,plain,(
% 0.22/0.58    spl4_36 | ~spl4_13 | ~spl4_30),
% 0.22/0.58    inference(avatar_split_clause,[],[f429,f372,f197,f465])).
% 0.22/0.58  fof(f197,plain,(
% 0.22/0.58    spl4_13 <=> ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(X0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.58  fof(f372,plain,(
% 0.22/0.58    spl4_30 <=> r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.58  fof(f429,plain,(
% 0.22/0.58    sK1 = k1_tarski(sK3(sK1)) | (~spl4_13 | ~spl4_30)),
% 0.22/0.58    inference(subsumption_resolution,[],[f425,f76])).
% 0.22/0.58  fof(f76,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.58  fof(f425,plain,(
% 0.22/0.58    sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(k1_tarski(sK3(sK1))) | (~spl4_13 | ~spl4_30)),
% 0.22/0.58    inference(resolution,[],[f374,f198])).
% 0.22/0.58  fof(f198,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(X0)) ) | ~spl4_13),
% 0.22/0.58    inference(avatar_component_clause,[],[f197])).
% 0.22/0.58  fof(f374,plain,(
% 0.22/0.58    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl4_30),
% 0.22/0.58    inference(avatar_component_clause,[],[f372])).
% 0.22/0.58  fof(f451,plain,(
% 0.22/0.58    spl4_34 | ~spl4_31),
% 0.22/0.58    inference(avatar_split_clause,[],[f418,f408,f448])).
% 0.22/0.58  fof(f408,plain,(
% 0.22/0.58    spl4_31 <=> r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.58  fof(f418,plain,(
% 0.22/0.58    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl4_31),
% 0.22/0.58    inference(resolution,[],[f410,f162])).
% 0.22/0.58  fof(f162,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f97,f94])).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f63])).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f64])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(nnf_transformation,[],[f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.58  fof(f410,plain,(
% 0.22/0.58    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl4_31),
% 0.22/0.58    inference(avatar_component_clause,[],[f408])).
% 0.22/0.58  fof(f411,plain,(
% 0.22/0.58    spl4_31 | spl4_5 | ~spl4_6),
% 0.22/0.58    inference(avatar_split_clause,[],[f406,f137,f132,f408])).
% 0.22/0.58  fof(f406,plain,(
% 0.22/0.58    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | (spl4_5 | ~spl4_6)),
% 0.22/0.58    inference(subsumption_resolution,[],[f402,f134])).
% 0.22/0.58  fof(f402,plain,(
% 0.22/0.58    v1_xboole_0(sK1) | r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl4_6),
% 0.22/0.58    inference(resolution,[],[f249,f139])).
% 0.22/0.58  fof(f249,plain,(
% 0.22/0.58    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(X5)) | v1_xboole_0(X4) | r2_hidden(sK3(X4),X5)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f247,f85])).
% 0.22/0.58  fof(f247,plain,(
% 0.22/0.58    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(X5)) | v1_xboole_0(X4) | r2_hidden(sK3(X4),X5) | v1_xboole_0(X5)) )),
% 0.22/0.58    inference(resolution,[],[f175,f96])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f64])).
% 0.22/0.58  fof(f381,plain,(
% 0.22/0.58    spl4_5 | spl4_29),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f380])).
% 0.22/0.58  fof(f380,plain,(
% 0.22/0.58    $false | (spl4_5 | spl4_29)),
% 0.22/0.58    inference(subsumption_resolution,[],[f377,f134])).
% 0.22/0.58  fof(f377,plain,(
% 0.22/0.58    v1_xboole_0(sK1) | spl4_29),
% 0.22/0.58    inference(resolution,[],[f370,f163])).
% 0.22/0.58  fof(f163,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(resolution,[],[f162,f95])).
% 0.22/0.58  fof(f370,plain,(
% 0.22/0.58    ~m1_subset_1(sK3(sK1),sK1) | spl4_29),
% 0.22/0.58    inference(avatar_component_clause,[],[f368])).
% 0.22/0.58  fof(f368,plain,(
% 0.22/0.58    spl4_29 <=> m1_subset_1(sK3(sK1),sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.58  fof(f375,plain,(
% 0.22/0.58    ~spl4_29 | spl4_30 | spl4_5 | ~spl4_25),
% 0.22/0.58    inference(avatar_split_clause,[],[f348,f336,f132,f372,f368])).
% 0.22/0.58  fof(f336,plain,(
% 0.22/0.58    spl4_25 <=> k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.58  fof(f348,plain,(
% 0.22/0.58    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~m1_subset_1(sK3(sK1),sK1) | (spl4_5 | ~spl4_25)),
% 0.22/0.58    inference(subsumption_resolution,[],[f345,f134])).
% 0.22/0.58  fof(f345,plain,(
% 0.22/0.58    r1_tarski(k1_tarski(sK3(sK1)),sK1) | v1_xboole_0(sK1) | ~m1_subset_1(sK3(sK1),sK1) | ~spl4_25),
% 0.22/0.58    inference(superposition,[],[f190,f338])).
% 0.22/0.58  fof(f338,plain,(
% 0.22/0.58    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1)) | ~spl4_25),
% 0.22/0.58    inference(avatar_component_clause,[],[f336])).
% 0.22/0.58  fof(f190,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.58    inference(resolution,[],[f101,f105])).
% 0.22/0.58  fof(f105,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.58    inference(nnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.58  fof(f361,plain,(
% 0.22/0.58    spl4_28 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f244,f127,f117,f112,f359])).
% 0.22/0.58  fof(f244,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f243,f114])).
% 0.22/0.58  fof(f243,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f242,f119])).
% 0.22/0.58  fof(f242,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_4),
% 0.22/0.58    inference(resolution,[],[f92,f129])).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | u1_struct_0(sK2(X0,X1)) = X1 | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f59])).
% 0.22/0.58  fof(f343,plain,(
% 0.22/0.58    spl4_26 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f239,f127,f117,f112,f341])).
% 0.22/0.58  fof(f239,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f238,f114])).
% 0.22/0.58  fof(f238,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f237,f119])).
% 0.22/0.58  fof(f237,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_4),
% 0.22/0.58    inference(resolution,[],[f91,f129])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | m1_pre_topc(sK2(X0,X1),X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f59])).
% 0.22/0.58  fof(f339,plain,(
% 0.22/0.58    spl4_25 | spl4_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f258,f132,f336])).
% 0.22/0.58  fof(f258,plain,(
% 0.22/0.58    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1)) | spl4_5),
% 0.22/0.58    inference(resolution,[],[f180,f134])).
% 0.22/0.58  fof(f180,plain,(
% 0.22/0.58    ( ! [X2] : (v1_xboole_0(X2) | k6_domain_1(X2,sK3(X2)) = k1_tarski(sK3(X2))) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f179])).
% 0.22/0.58  fof(f179,plain,(
% 0.22/0.58    ( ! [X2] : (k6_domain_1(X2,sK3(X2)) = k1_tarski(sK3(X2)) | v1_xboole_0(X2) | v1_xboole_0(X2)) )),
% 0.22/0.58    inference(resolution,[],[f100,f163])).
% 0.22/0.58  fof(f328,plain,(
% 0.22/0.58    spl4_24 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_22),
% 0.22/0.58    inference(avatar_split_clause,[],[f315,f294,f142,f137,f132,f325])).
% 0.22/0.58  fof(f294,plain,(
% 0.22/0.58    spl4_22 <=> ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.58  fof(f315,plain,(
% 0.22/0.58    v1_tdlat_3(sK2(sK0,sK1)) | (spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_22)),
% 0.22/0.58    inference(subsumption_resolution,[],[f314,f134])).
% 0.22/0.58  fof(f314,plain,(
% 0.22/0.58    v1_xboole_0(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | (~spl4_6 | ~spl4_7 | ~spl4_22)),
% 0.22/0.58    inference(subsumption_resolution,[],[f312,f139])).
% 0.22/0.58  fof(f312,plain,(
% 0.22/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | (~spl4_7 | ~spl4_22)),
% 0.22/0.58    inference(resolution,[],[f295,f144])).
% 0.22/0.58  fof(f295,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0))) ) | ~spl4_22),
% 0.22/0.58    inference(avatar_component_clause,[],[f294])).
% 0.22/0.58  fof(f296,plain,(
% 0.22/0.58    spl4_22 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f235,f127,f117,f112,f294])).
% 0.22/0.58  fof(f235,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0))) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f234,f114])).
% 0.22/0.58  fof(f234,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f233,f119])).
% 0.22/0.58  fof(f233,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_4),
% 0.22/0.58    inference(resolution,[],[f90,f129])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | v1_tdlat_3(sK2(X0,X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f59])).
% 0.22/0.58  fof(f199,plain,(
% 0.22/0.58    spl4_13 | spl4_5 | ~spl4_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f195,f146,f132,f197])).
% 0.22/0.58  fof(f195,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(X0)) ) | (spl4_5 | ~spl4_8)),
% 0.22/0.58    inference(subsumption_resolution,[],[f193,f134])).
% 0.22/0.58  fof(f193,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(sK1) | v1_xboole_0(X0)) ) | ~spl4_8),
% 0.22/0.58    inference(resolution,[],[f77,f148])).
% 0.22/0.58  fof(f148,plain,(
% 0.22/0.58    v1_zfmisc_1(sK1) | ~spl4_8),
% 0.22/0.58    inference(avatar_component_clause,[],[f146])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,axiom,(
% 0.22/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.58  fof(f151,plain,(
% 0.22/0.58    ~spl4_7 | ~spl4_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f150,f146,f142])).
% 0.22/0.58  fof(f150,plain,(
% 0.22/0.58    ~v2_tex_2(sK1,sK0) | ~spl4_8),
% 0.22/0.58    inference(subsumption_resolution,[],[f75,f148])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f53])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,negated_conjecture,(
% 0.22/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.58    inference(negated_conjecture,[],[f21])).
% 0.22/0.58  fof(f21,conjecture,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.58  fof(f149,plain,(
% 0.22/0.58    spl4_7 | spl4_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f74,f146,f142])).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    spl4_6),
% 0.22/0.58    inference(avatar_split_clause,[],[f73,f137])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    ~spl4_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f72,f132])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ~v1_xboole_0(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f130,plain,(
% 0.22/0.58    spl4_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f71,f127])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    l1_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    spl4_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f70,f122])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    v2_tdlat_3(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f120,plain,(
% 0.22/0.58    spl4_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f69,f117])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    v2_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    ~spl4_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f68,f112])).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    ~v2_struct_0(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (2254)------------------------------
% 0.22/0.58  % (2254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (2254)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (2254)Memory used [KB]: 6908
% 0.22/0.58  % (2254)Time elapsed: 0.156 s
% 0.22/0.58  % (2254)------------------------------
% 0.22/0.58  % (2254)------------------------------
% 0.22/0.58  % (2246)Success in time 0.218 s
%------------------------------------------------------------------------------
