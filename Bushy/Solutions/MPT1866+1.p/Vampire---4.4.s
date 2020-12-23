%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t34_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:31 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  558 (1660 expanded)
%              Number of leaves         :  129 ( 678 expanded)
%              Depth                    :   15
%              Number of atoms          : 2077 (5710 expanded)
%              Number of equality atoms :   66 ( 429 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :   13 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1412,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f334,f341,f348,f355,f362,f369,f376,f383,f390,f397,f404,f411,f418,f425,f432,f439,f446,f453,f460,f467,f474,f481,f488,f495,f502,f509,f516,f523,f530,f537,f544,f551,f558,f565,f572,f579,f606,f625,f650,f665,f718,f738,f764,f783,f786,f794,f814,f845,f856,f867,f878,f890,f909,f923,f956,f975,f986,f997,f1008,f1020,f1034,f1057,f1062,f1067,f1072,f1078,f1105,f1109,f1113,f1117,f1126,f1135,f1144,f1153,f1168,f1180,f1201,f1213,f1219,f1224,f1242,f1249,f1256,f1263,f1270,f1277,f1293,f1300,f1307,f1314,f1321,f1328,f1338,f1346,f1373,f1396,f1402,f1407,f1411])).

fof(f1411,plain,
    ( ~ spl22_91
    | spl22_83
    | ~ spl22_84
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f1410,f812,f762,f736,f716,f781])).

fof(f781,plain,
    ( spl22_91
  <=> ~ v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_91])])).

fof(f716,plain,
    ( spl22_83
  <=> ~ v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_83])])).

fof(f736,plain,
    ( spl22_84
  <=> v1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_84])])).

fof(f762,plain,
    ( spl22_86
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_86])])).

fof(f812,plain,
    ( spl22_94
  <=> u1_struct_0(sK2(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_94])])).

fof(f1410,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl22_83
    | ~ spl22_84
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1409,f717])).

fof(f717,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_83 ),
    inference(avatar_component_clause,[],[f716])).

fof(f1409,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_84
    | ~ spl22_86
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1408,f763])).

fof(f763,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_86 ),
    inference(avatar_component_clause,[],[f762])).

fof(f1408,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_84
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f826,f737])).

fof(f737,plain,
    ( v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_84 ),
    inference(avatar_component_clause,[],[f736])).

fof(f826,plain,
    ( ~ v1_pre_topc(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_94 ),
    inference(trivial_inequality_removal,[],[f816])).

fof(f816,plain,
    ( sK1 != sK1
    | ~ v1_pre_topc(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_94 ),
    inference(superposition,[],[f251,f813])).

fof(f813,plain,
    ( u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_94 ),
    inference(avatar_component_clause,[],[f812])).

fof(f251,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK1
      | ~ v1_pre_topc(X2)
      | ~ v1_tdlat_3(X2)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f222])).

fof(f222,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f221])).

fof(f221,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => u1_struct_0(X2) != X1 )
                & v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',t34_tex_2)).

fof(f1407,plain,
    ( spl22_90
    | spl22_194
    | spl22_83
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f1403,f812,f716,f1405,f778])).

fof(f778,plain,
    ( spl22_90
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_90])])).

fof(f1405,plain,
    ( spl22_194
  <=> ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_194])])).

fof(f1403,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | v1_tdlat_3(sK2(sK0,sK1)) )
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f1187,f813])).

fof(f1187,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) )
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1181,f717])).

fof(f1181,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) )
    | ~ spl22_94 ),
    inference(superposition,[],[f326,f813])).

fof(f326,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f288])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f244])).

fof(f244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f243])).

fof(f243,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f213])).

fof(f213,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',t26_tex_2)).

fof(f1402,plain,
    ( ~ spl22_91
    | spl22_192
    | spl22_83
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f1398,f812,f716,f1400,f781])).

fof(f1400,plain,
    ( spl22_192
  <=> ! [X0] :
        ( v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_192])])).

fof(f1398,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | ~ v1_tdlat_3(sK2(sK0,sK1)) )
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f1397,f813])).

fof(f1397,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | ~ v1_tdlat_3(sK2(sK0,sK1))
        | v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) )
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1350,f717])).

fof(f1350,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | ~ v1_tdlat_3(sK2(sK0,sK1))
        | v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) )
    | ~ spl22_94 ),
    inference(superposition,[],[f327,f813])).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f287])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f244])).

fof(f1396,plain,
    ( ~ spl22_0
    | spl22_5
    | ~ spl22_6
    | ~ spl22_8
    | spl22_83
    | ~ spl22_86
    | spl22_91
    | ~ spl22_94 ),
    inference(avatar_contradiction_clause,[],[f1395])).

fof(f1395,plain,
    ( $false
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_6
    | ~ spl22_8
    | ~ spl22_83
    | ~ spl22_86
    | ~ spl22_91
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1394,f347])).

fof(f347,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl22_5 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl22_5
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5])])).

fof(f1394,plain,
    ( v2_struct_0(sK0)
    | ~ spl22_0
    | ~ spl22_6
    | ~ spl22_8
    | ~ spl22_83
    | ~ spl22_86
    | ~ spl22_91
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1393,f354])).

fof(f354,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl22_6 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl22_6
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_6])])).

fof(f1393,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_83
    | ~ spl22_86
    | ~ spl22_91
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1392,f333])).

fof(f333,plain,
    ( l1_pre_topc(sK0)
    | ~ spl22_0 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl22_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_0])])).

fof(f1392,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl22_8
    | ~ spl22_83
    | ~ spl22_86
    | ~ spl22_91
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1391,f361])).

fof(f361,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_8 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl22_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_8])])).

fof(f1391,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl22_83
    | ~ spl22_86
    | ~ spl22_91
    | ~ spl22_94 ),
    inference(resolution,[],[f1189,f763])).

fof(f1189,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0) )
    | ~ spl22_83
    | ~ spl22_91
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f1188,f813])).

fof(f1188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | ~ v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) )
    | ~ spl22_83
    | ~ spl22_91
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1187,f782])).

fof(f782,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl22_91 ),
    inference(avatar_component_clause,[],[f781])).

fof(f1373,plain,
    ( ~ spl22_191
    | spl22_107
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1366,f1240,f898,f1371])).

fof(f1371,plain,
    ( spl22_191
  <=> u1_struct_0(sK2(sK2(sK0,sK1),sK13)) != sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_191])])).

fof(f898,plain,
    ( spl22_107
  <=> u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) != sK10(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_107])])).

fof(f1240,plain,
    ( spl22_162
  <=> sK10(k1_zfmisc_1(sK1)) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_162])])).

fof(f1366,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK1),sK13)) != sK13
    | ~ spl22_107
    | ~ spl22_162 ),
    inference(forward_demodulation,[],[f899,f1241])).

fof(f1241,plain,
    ( sK10(k1_zfmisc_1(sK1)) = sK13
    | ~ spl22_162 ),
    inference(avatar_component_clause,[],[f1240])).

fof(f899,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) != sK10(k1_zfmisc_1(sK1))
    | ~ spl22_107 ),
    inference(avatar_component_clause,[],[f898])).

fof(f1346,plain,
    ( ~ spl22_189
    | spl22_159
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1339,f1240,f1205,f1344])).

fof(f1344,plain,
    ( spl22_189
  <=> ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_189])])).

fof(f1205,plain,
    ( spl22_159
  <=> ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_159])])).

fof(f1339,plain,
    ( ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK13))
    | ~ spl22_159
    | ~ spl22_162 ),
    inference(forward_demodulation,[],[f1206,f1241])).

fof(f1206,plain,
    ( ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_159 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f1338,plain,
    ( ~ spl22_187
    | spl22_131
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1331,f1240,f1091,f1336])).

fof(f1336,plain,
    ( spl22_187
  <=> ~ v2_struct_0(sK2(sK2(sK0,sK1),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_187])])).

fof(f1091,plain,
    ( spl22_131
  <=> ~ v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_131])])).

fof(f1331,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK13))
    | ~ spl22_131
    | ~ spl22_162 ),
    inference(forward_demodulation,[],[f1092,f1241])).

fof(f1092,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_131 ),
    inference(avatar_component_clause,[],[f1091])).

fof(f1328,plain,
    ( ~ spl22_185
    | spl22_153
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1284,f1240,f1163,f1326])).

fof(f1326,plain,
    ( spl22_185
  <=> ~ v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_185])])).

fof(f1163,plain,
    ( spl22_153
  <=> ~ v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_153])])).

fof(f1284,plain,
    ( ~ v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13)))
    | ~ spl22_153
    | ~ spl22_162 ),
    inference(backward_demodulation,[],[f1241,f1164])).

fof(f1164,plain,
    ( ~ v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_153 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f1321,plain,
    ( spl22_182
    | ~ spl22_150
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1283,f1240,f1157,f1319])).

fof(f1319,plain,
    ( spl22_182
  <=> v2_pre_topc(sK2(sK2(sK0,sK1),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_182])])).

fof(f1157,plain,
    ( spl22_150
  <=> v2_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_150])])).

fof(f1283,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK13))
    | ~ spl22_150
    | ~ spl22_162 ),
    inference(backward_demodulation,[],[f1241,f1158])).

fof(f1158,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_150 ),
    inference(avatar_component_clause,[],[f1157])).

fof(f1314,plain,
    ( ~ spl22_181
    | spl22_149
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1282,f1240,f1148,f1312])).

fof(f1312,plain,
    ( spl22_181
  <=> ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_181])])).

fof(f1148,plain,
    ( spl22_149
  <=> ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_149])])).

fof(f1282,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13)))
    | ~ spl22_149
    | ~ spl22_162 ),
    inference(backward_demodulation,[],[f1241,f1149])).

fof(f1149,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_149 ),
    inference(avatar_component_clause,[],[f1148])).

fof(f1307,plain,
    ( ~ spl22_179
    | spl22_145
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1281,f1240,f1130,f1305])).

fof(f1305,plain,
    ( spl22_179
  <=> ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_179])])).

fof(f1130,plain,
    ( spl22_145
  <=> ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_145])])).

fof(f1281,plain,
    ( ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13)))
    | ~ spl22_145
    | ~ spl22_162 ),
    inference(backward_demodulation,[],[f1241,f1131])).

fof(f1131,plain,
    ( ~ v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_145 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1300,plain,
    ( ~ spl22_177
    | spl22_143
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1280,f1240,f1124,f1298])).

fof(f1298,plain,
    ( spl22_177
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_177])])).

fof(f1124,plain,
    ( spl22_143
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_143])])).

fof(f1280,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK13),sK12(sK13)))
    | ~ spl22_143
    | ~ spl22_162 ),
    inference(backward_demodulation,[],[f1241,f1125])).

fof(f1125,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_143 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f1293,plain,
    ( ~ spl22_175
    | spl22_133
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1279,f1240,f1100,f1291])).

fof(f1291,plain,
    ( spl22_175
  <=> ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_175])])).

fof(f1100,plain,
    ( spl22_133
  <=> ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_133])])).

fof(f1279,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK13))
    | ~ spl22_133
    | ~ spl22_162 ),
    inference(backward_demodulation,[],[f1241,f1101])).

fof(f1101,plain,
    ( ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_133 ),
    inference(avatar_component_clause,[],[f1100])).

fof(f1277,plain,
    ( spl22_172
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(avatar_split_clause,[],[f1235,f907,f437,f1275])).

fof(f1275,plain,
    ( spl22_172
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_172])])).

fof(f437,plain,
    ( spl22_30
  <=> v1_xboole_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_30])])).

fof(f907,plain,
    ( spl22_108
  <=> v1_xboole_0(sK10(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_108])])).

fof(f1235,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(resolution,[],[f908,f721])).

fof(f721,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))))))))) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f696,f596])).

fof(f596,plain,(
    ! [X0] :
      ( v1_xboole_0(sK10(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f292,f289])).

fof(f289,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',existence_m1_subset_1)).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f245])).

fof(f245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',cc1_subset_1)).

fof(f696,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))))))) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f635,f596])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))))) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f618,f596])).

fof(f618,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f607,f596])).

fof(f607,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK10(k1_zfmisc_1(X0)) = sK13 )
    | ~ spl22_30 ),
    inference(resolution,[],[f596,f580])).

fof(f580,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK13 = X0 )
    | ~ spl22_30 ),
    inference(resolution,[],[f258,f438])).

fof(f438,plain,
    ( v1_xboole_0(sK13)
    | ~ spl22_30 ),
    inference(avatar_component_clause,[],[f437])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f220])).

fof(f220,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',t8_boole)).

fof(f908,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ spl22_108 ),
    inference(avatar_component_clause,[],[f907])).

fof(f1270,plain,
    ( spl22_170
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(avatar_split_clause,[],[f1233,f907,f437,f1268])).

fof(f1268,plain,
    ( spl22_170
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_170])])).

fof(f1233,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))))) = sK13
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(resolution,[],[f908,f696])).

fof(f1263,plain,
    ( spl22_168
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(avatar_split_clause,[],[f1231,f907,f437,f1261])).

fof(f1261,plain,
    ( spl22_168
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_168])])).

fof(f1231,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))))) = sK13
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(resolution,[],[f908,f635])).

fof(f1256,plain,
    ( spl22_166
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(avatar_split_clause,[],[f1229,f907,f437,f1254])).

fof(f1254,plain,
    ( spl22_166
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_166])])).

fof(f1229,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))))) = sK13
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(resolution,[],[f908,f618])).

fof(f1249,plain,
    ( spl22_164
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(avatar_split_clause,[],[f1227,f907,f437,f1247])).

fof(f1247,plain,
    ( spl22_164
  <=> sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_164])])).

fof(f1227,plain,
    ( sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK1)))) = sK13
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(resolution,[],[f908,f607])).

fof(f1242,plain,
    ( spl22_162
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(avatar_split_clause,[],[f1226,f907,f437,f1240])).

fof(f1226,plain,
    ( sK10(k1_zfmisc_1(sK1)) = sK13
    | ~ spl22_30
    | ~ spl22_108 ),
    inference(resolution,[],[f908,f580])).

fof(f1224,plain,
    ( spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | spl22_109
    | ~ spl22_130 ),
    inference(avatar_contradiction_clause,[],[f1223])).

fof(f1223,plain,
    ( $false
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_109
    | ~ spl22_130 ),
    inference(subsumption_resolution,[],[f1222,f289])).

fof(f1222,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_109
    | ~ spl22_130 ),
    inference(subsumption_resolution,[],[f1221,f905])).

fof(f905,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ spl22_109 ),
    inference(avatar_component_clause,[],[f904])).

fof(f904,plain,
    ( spl22_109
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_109])])).

fof(f1221,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_130 ),
    inference(resolution,[],[f1095,f828])).

fof(f828,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK2(sK2(sK0,sK1),X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f827,f717])).

fof(f827,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v1_xboole_0(X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ v2_struct_0(sK2(sK2(sK0,sK1),X0)) )
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f817,f793])).

fof(f793,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_92 ),
    inference(avatar_component_clause,[],[f792])).

fof(f792,plain,
    ( spl22_92
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_92])])).

fof(f817,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | v1_xboole_0(X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ v2_struct_0(sK2(sK2(sK0,sK1),X0)) )
    | ~ spl22_94 ),
    inference(superposition,[],[f259,f813])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f224])).

fof(f224,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f211])).

fof(f211,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',t10_tsep_1)).

fof(f1095,plain,
    ( v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_130 ),
    inference(avatar_component_clause,[],[f1094])).

fof(f1094,plain,
    ( spl22_130
  <=> v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_130])])).

fof(f1219,plain,
    ( spl22_158
    | spl22_130
    | spl22_160
    | ~ spl22_106 ),
    inference(avatar_split_clause,[],[f1218,f901,f1211,f1094,f1208])).

fof(f1208,plain,
    ( spl22_158
  <=> v1_tdlat_3(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_158])])).

fof(f1211,plain,
    ( spl22_160
  <=> ! [X2] :
        ( ~ v2_tex_2(sK10(k1_zfmisc_1(sK1)),X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_160])])).

fof(f901,plain,
    ( spl22_106
  <=> u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) = sK10(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_106])])).

fof(f1218,plain,
    ( ! [X2] :
        ( ~ v2_tex_2(sK10(k1_zfmisc_1(sK1)),X2)
        | ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2)
        | v2_struct_0(X2)
        | v1_tdlat_3(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) )
    | ~ spl22_106 ),
    inference(forward_demodulation,[],[f1183,f902])).

fof(f902,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) = sK10(k1_zfmisc_1(sK1))
    | ~ spl22_106 ),
    inference(avatar_component_clause,[],[f901])).

fof(f1183,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2)
        | v2_struct_0(X2)
        | v1_tdlat_3(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ v2_tex_2(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))),X2) )
    | ~ spl22_106 ),
    inference(superposition,[],[f326,f902])).

fof(f1213,plain,
    ( spl22_158
    | spl22_160
    | ~ spl22_106
    | spl22_131 ),
    inference(avatar_split_clause,[],[f1203,f1091,f901,f1211,f1208])).

fof(f1203,plain,
    ( ! [X2] :
        ( ~ v2_tex_2(sK10(k1_zfmisc_1(sK1)),X2)
        | ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2)
        | v2_struct_0(X2)
        | v1_tdlat_3(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) )
    | ~ spl22_106
    | ~ spl22_131 ),
    inference(forward_demodulation,[],[f1202,f902])).

fof(f1202,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2)
        | v2_struct_0(X2)
        | v1_tdlat_3(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ v2_tex_2(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))),X2) )
    | ~ spl22_106
    | ~ spl22_131 ),
    inference(subsumption_resolution,[],[f1183,f1092])).

fof(f1201,plain,
    ( spl22_154
    | spl22_156
    | spl22_97
    | ~ spl22_110 ),
    inference(avatar_split_clause,[],[f1191,f915,f843,f1199,f1196])).

fof(f1196,plain,
    ( spl22_154
  <=> v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_154])])).

fof(f1199,plain,
    ( spl22_156
  <=> ! [X1] :
        ( ~ v2_tex_2(sK12(sK1),X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK12(sK1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_156])])).

fof(f843,plain,
    ( spl22_97
  <=> ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_97])])).

fof(f915,plain,
    ( spl22_110
  <=> u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) = sK12(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_110])])).

fof(f1191,plain,
    ( ! [X1] :
        ( ~ v2_tex_2(sK12(sK1),X1)
        | ~ m1_subset_1(sK12(sK1),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),X1)
        | v2_struct_0(X1)
        | v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1))) )
    | ~ spl22_97
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1190,f916])).

fof(f916,plain,
    ( u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) = sK12(sK1)
    | ~ spl22_110 ),
    inference(avatar_component_clause,[],[f915])).

fof(f1190,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK12(sK1),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),X1)
        | v2_struct_0(X1)
        | v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1)))
        | ~ v2_tex_2(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))),X1) )
    | ~ spl22_97
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1182,f844])).

fof(f844,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_97 ),
    inference(avatar_component_clause,[],[f843])).

fof(f1182,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK12(sK1),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
        | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),X1)
        | v2_struct_0(X1)
        | v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1)))
        | ~ v2_tex_2(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))),X1) )
    | ~ spl22_110 ),
    inference(superposition,[],[f326,f916])).

fof(f1180,plain,
    ( spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94
    | spl22_109
    | spl22_151 ),
    inference(avatar_contradiction_clause,[],[f1179])).

fof(f1179,plain,
    ( $false
    | ~ spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_109
    | ~ spl22_151 ),
    inference(subsumption_resolution,[],[f1178,f905])).

fof(f1178,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_151 ),
    inference(subsumption_resolution,[],[f1177,f289])).

fof(f1177,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))
    | v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94
    | ~ spl22_151 ),
    inference(resolution,[],[f1175,f1161])).

fof(f1161,plain,
    ( ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_151 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f1160,plain,
    ( spl22_151
  <=> ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_151])])).

fof(f1175,plain,
    ( ! [X1] :
        ( v2_pre_topc(sK2(sK2(sK0,sK1),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | v1_xboole_0(X1) )
    | ~ spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1174,f776])).

fof(f776,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_88 ),
    inference(avatar_component_clause,[],[f775])).

fof(f775,plain,
    ( spl22_88
  <=> v2_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_88])])).

fof(f1174,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ v2_pre_topc(sK2(sK0,sK1))
        | v2_pre_topc(sK2(sK2(sK0,sK1),X1)) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f1170,f793])).

fof(f1170,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | ~ v2_pre_topc(sK2(sK0,sK1))
        | v2_pre_topc(sK2(sK2(sK0,sK1),X1)) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(resolution,[],[f832,f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f227])).

fof(f227,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',cc1_pre_topc)).

fof(f832,plain,
    ( ! [X2] :
        ( m1_pre_topc(sK2(sK2(sK0,sK1),X2),sK2(sK0,sK1))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK1)) )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f831,f717])).

fof(f831,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | v1_xboole_0(X2)
        | v2_struct_0(sK2(sK0,sK1))
        | m1_pre_topc(sK2(sK2(sK0,sK1),X2),sK2(sK0,sK1)) )
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f819,f793])).

fof(f819,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | v1_xboole_0(X2)
        | v2_struct_0(sK2(sK0,sK1))
        | m1_pre_topc(sK2(sK2(sK0,sK1),X2),sK2(sK0,sK1)) )
    | ~ spl22_94 ),
    inference(superposition,[],[f261,f813])).

fof(f261,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f1168,plain,
    ( spl22_130
    | ~ spl22_151
    | ~ spl22_133
    | spl22_152
    | ~ spl22_106
    | spl22_109 ),
    inference(avatar_split_clause,[],[f1155,f904,f901,f1166,f1100,f1160,f1094])).

fof(f1166,plain,
    ( spl22_152
  <=> v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_152])])).

fof(f1155,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106
    | ~ spl22_109 ),
    inference(subsumption_resolution,[],[f1154,f905])).

fof(f1154,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106 ),
    inference(forward_demodulation,[],[f1088,f902])).

fof(f1088,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106 ),
    inference(superposition,[],[f799,f902])).

fof(f799,plain,(
    ! [X1] :
      ( v2_pre_topc(sK2(X1,sK12(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f796])).

fof(f796,plain,(
    ! [X1] :
      ( v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_pre_topc(sK2(X1,sK12(u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f765,f263])).

fof(f765,plain,(
    ! [X1] :
      ( m1_pre_topc(sK2(X1,sK12(u1_struct_0(X1))),X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f753,f294])).

fof(f294,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK12(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f246])).

fof(f246,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f150])).

fof(f150,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc1_subset_1)).

fof(f753,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v1_xboole_0(sK12(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | m1_pre_topc(sK2(X1,sK12(u1_struct_0(X1))),X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f261,f293])).

fof(f293,plain,(
    ! [X0] :
      ( m1_subset_1(sK12(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f246])).

fof(f1153,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_148
    | ~ spl22_106
    | spl22_109 ),
    inference(avatar_split_clause,[],[f1146,f904,f901,f1151,f1100,f1094])).

fof(f1151,plain,
    ( spl22_148
  <=> l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_148])])).

fof(f1146,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106
    | ~ spl22_109 ),
    inference(subsumption_resolution,[],[f1145,f905])).

fof(f1145,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106 ),
    inference(forward_demodulation,[],[f1087,f902])).

fof(f1087,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106 ),
    inference(superposition,[],[f798,f902])).

fof(f798,plain,(
    ! [X2] :
      ( l1_pre_topc(sK2(X2,sK12(u1_struct_0(X2))))
      | ~ l1_pre_topc(X2)
      | v1_xboole_0(u1_struct_0(X2))
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f797])).

fof(f797,plain,(
    ! [X2] :
      ( v2_struct_0(X2)
      | ~ l1_pre_topc(X2)
      | v1_xboole_0(u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | l1_pre_topc(sK2(X2,sK12(u1_struct_0(X2)))) ) ),
    inference(resolution,[],[f765,f265])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f229])).

fof(f229,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',dt_m1_pre_topc)).

fof(f1144,plain,
    ( ~ spl22_133
    | spl22_130
    | spl22_146
    | ~ spl22_106
    | spl22_109 ),
    inference(avatar_split_clause,[],[f1137,f904,f901,f1142,f1094,f1100])).

fof(f1142,plain,
    ( spl22_146
  <=> m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_146])])).

fof(f1137,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106
    | ~ spl22_109 ),
    inference(subsumption_resolution,[],[f1136,f905])).

fof(f1136,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106 ),
    inference(forward_demodulation,[],[f1086,f902])).

fof(f1086,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_106 ),
    inference(superposition,[],[f765,f902])).

fof(f1135,plain,
    ( ~ spl22_133
    | spl22_130
    | spl22_144
    | ~ spl22_106
    | spl22_109 ),
    inference(avatar_split_clause,[],[f1128,f904,f901,f1133,f1094,f1100])).

fof(f1133,plain,
    ( spl22_144
  <=> v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_144])])).

fof(f1128,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106
    | ~ spl22_109 ),
    inference(subsumption_resolution,[],[f1127,f905])).

fof(f1127,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106 ),
    inference(forward_demodulation,[],[f1085,f902])).

fof(f1085,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_106 ),
    inference(superposition,[],[f739,f902])).

fof(f739,plain,(
    ! [X1] :
      ( v1_pre_topc(sK2(X1,sK12(u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f727,f294])).

fof(f727,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v1_xboole_0(sK12(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | v1_pre_topc(sK2(X1,sK12(u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f260,f293])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_pre_topc(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f1126,plain,
    ( ~ spl22_133
    | spl22_130
    | ~ spl22_143
    | ~ spl22_106
    | spl22_109 ),
    inference(avatar_split_clause,[],[f1119,f904,f901,f1124,f1094,f1100])).

fof(f1119,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106
    | ~ spl22_109 ),
    inference(subsumption_resolution,[],[f1118,f905])).

fof(f1118,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ spl22_106 ),
    inference(forward_demodulation,[],[f1084,f902])).

fof(f1084,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),sK12(sK10(k1_zfmisc_1(sK1)))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))))
    | ~ spl22_106 ),
    inference(superposition,[],[f719,f902])).

fof(f719,plain,(
    ! [X1] :
      ( ~ v2_struct_0(sK2(X1,sK12(u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f707,f294])).

fof(f707,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v1_xboole_0(sK12(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ v2_struct_0(sK2(X1,sK12(u1_struct_0(X1))))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f259,f293])).

fof(f1117,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_140
    | ~ spl22_106 ),
    inference(avatar_split_clause,[],[f1083,f901,f1115,f1100,f1094])).

fof(f1115,plain,
    ( spl22_140
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X3)) = X3
        | v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_140])])).

fof(f1083,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | u1_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X3)) = X3 )
    | ~ spl22_106 ),
    inference(superposition,[],[f262,f902])).

fof(f262,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f225])).

fof(f1113,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_138
    | ~ spl22_106 ),
    inference(avatar_split_clause,[],[f1082,f901,f1111,f1100,f1094])).

fof(f1111,plain,
    ( spl22_138
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_138])])).

fof(f1082,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X2)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X2),sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) )
    | ~ spl22_106 ),
    inference(superposition,[],[f261,f902])).

fof(f1109,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_136
    | ~ spl22_106 ),
    inference(avatar_split_clause,[],[f1081,f901,f1107,f1100,f1094])).

fof(f1107,plain,
    ( spl22_136
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X1))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_136])])).

fof(f1081,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X1)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X1)) )
    | ~ spl22_106 ),
    inference(superposition,[],[f260,f902])).

fof(f1105,plain,
    ( spl22_130
    | ~ spl22_133
    | spl22_134
    | ~ spl22_106 ),
    inference(avatar_split_clause,[],[f1080,f901,f1103,f1100,f1094])).

fof(f1103,plain,
    ( spl22_134
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_134])])).

fof(f1080,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(sK1))))
        | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | v1_xboole_0(X0)
        | v2_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))))
        | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1))),X0)) )
    | ~ spl22_106 ),
    inference(superposition,[],[f259,f902])).

fof(f1078,plain,
    ( spl22_128
    | spl22_97
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1077,f918,f915,f888,f876,f843,f1018])).

fof(f1018,plain,
    ( spl22_128
  <=> v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_128])])).

fof(f876,plain,
    ( spl22_102
  <=> l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_102])])).

fof(f888,plain,
    ( spl22_104
  <=> v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_104])])).

fof(f918,plain,
    ( spl22_113
  <=> ~ v1_xboole_0(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_113])])).

fof(f1077,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1076,f919])).

fof(f919,plain,
    ( ~ v1_xboole_0(sK12(sK1))
    | ~ spl22_113 ),
    inference(avatar_component_clause,[],[f918])).

fof(f1076,plain,
    ( v1_xboole_0(sK12(sK1))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1075,f916])).

fof(f1075,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1074,f844])).

fof(f1074,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1073,f889])).

fof(f889,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_104 ),
    inference(avatar_component_clause,[],[f888])).

fof(f1073,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1044,f877])).

fof(f877,plain,
    ( l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102 ),
    inference(avatar_component_clause,[],[f876])).

fof(f1044,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_110 ),
    inference(superposition,[],[f799,f916])).

fof(f1072,plain,
    ( spl22_126
    | spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1071,f918,f915,f876,f843,f1006])).

fof(f1006,plain,
    ( spl22_126
  <=> l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_126])])).

fof(f1071,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1070,f919])).

fof(f1070,plain,
    ( v1_xboole_0(sK12(sK1))
    | l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1069,f916])).

fof(f1069,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1068,f844])).

fof(f1068,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1043,f877])).

fof(f1043,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_110 ),
    inference(superposition,[],[f798,f916])).

fof(f1067,plain,
    ( spl22_124
    | spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1066,f918,f915,f876,f843,f995])).

fof(f995,plain,
    ( spl22_124
  <=> m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_124])])).

fof(f1066,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1065,f919])).

fof(f1065,plain,
    ( v1_xboole_0(sK12(sK1))
    | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1064,f916])).

fof(f1064,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1063,f877])).

fof(f1063,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1042,f844])).

fof(f1042,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_110 ),
    inference(superposition,[],[f765,f916])).

fof(f1062,plain,
    ( spl22_122
    | spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1061,f918,f915,f876,f843,f984])).

fof(f984,plain,
    ( spl22_122
  <=> v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_122])])).

fof(f1061,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1060,f919])).

fof(f1060,plain,
    ( v1_xboole_0(sK12(sK1))
    | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1059,f916])).

fof(f1059,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1058,f877])).

fof(f1058,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1041,f844])).

fof(f1041,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_110 ),
    inference(superposition,[],[f739,f916])).

fof(f1057,plain,
    ( ~ spl22_121
    | spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1056,f918,f915,f876,f843,f973])).

fof(f973,plain,
    ( spl22_121
  <=> ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_121])])).

fof(f1056,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1055,f919])).

fof(f1055,plain,
    ( v1_xboole_0(sK12(sK1))
    | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1054,f916])).

fof(f1054,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1053,f877])).

fof(f1053,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1040,f844])).

fof(f1040,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_110 ),
    inference(superposition,[],[f719,f916])).

fof(f1034,plain,
    ( spl22_11
    | ~ spl22_112 ),
    inference(avatar_contradiction_clause,[],[f1033])).

fof(f1033,plain,
    ( $false
    | ~ spl22_11
    | ~ spl22_112 ),
    inference(subsumption_resolution,[],[f1021,f368])).

fof(f368,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl22_11 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl22_11
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_11])])).

fof(f1021,plain,
    ( v1_xboole_0(sK1)
    | ~ spl22_112 ),
    inference(resolution,[],[f922,f294])).

fof(f922,plain,
    ( v1_xboole_0(sK12(sK1))
    | ~ spl22_112 ),
    inference(avatar_component_clause,[],[f921])).

fof(f921,plain,
    ( spl22_112
  <=> v1_xboole_0(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_112])])).

fof(f1020,plain,
    ( spl22_128
    | spl22_97
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1013,f918,f915,f888,f876,f843,f1018])).

fof(f1013,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1012,f919])).

fof(f1012,plain,
    ( v1_xboole_0(sK12(sK1))
    | v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f1011,f916])).

fof(f1011,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1010,f844])).

fof(f1010,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102
    | ~ spl22_104
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f1009,f889])).

fof(f1009,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f934,f877])).

fof(f934,plain,
    ( v2_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_110 ),
    inference(superposition,[],[f799,f916])).

fof(f1008,plain,
    ( spl22_126
    | spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f1001,f918,f915,f876,f843,f1006])).

fof(f1001,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f1000,f919])).

fof(f1000,plain,
    ( v1_xboole_0(sK12(sK1))
    | l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f999,f916])).

fof(f999,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f998,f844])).

fof(f998,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f933,f877])).

fof(f933,plain,
    ( l1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_110 ),
    inference(superposition,[],[f798,f916])).

fof(f997,plain,
    ( spl22_124
    | spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f990,f918,f915,f876,f843,f995])).

fof(f990,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f989,f919])).

fof(f989,plain,
    ( v1_xboole_0(sK12(sK1))
    | m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f988,f916])).

fof(f988,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f987,f877])).

fof(f987,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f932,f844])).

fof(f932,plain,
    ( m1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))),sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_110 ),
    inference(superposition,[],[f765,f916])).

fof(f986,plain,
    ( spl22_122
    | spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f979,f918,f915,f876,f843,f984])).

fof(f979,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f978,f919])).

fof(f978,plain,
    ( v1_xboole_0(sK12(sK1))
    | v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f977,f916])).

fof(f977,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f976,f877])).

fof(f976,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f931,f844])).

fof(f931,plain,
    ( v1_pre_topc(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_110 ),
    inference(superposition,[],[f739,f916])).

fof(f975,plain,
    ( ~ spl22_121
    | spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | spl22_113 ),
    inference(avatar_split_clause,[],[f968,f918,f915,f876,f843,f973])).

fof(f968,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110
    | ~ spl22_113 ),
    inference(subsumption_resolution,[],[f967,f919])).

fof(f967,plain,
    ( v1_xboole_0(sK12(sK1))
    | ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(forward_demodulation,[],[f966,f916])).

fof(f966,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_102
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f965,f877])).

fof(f965,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_97
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f930,f844])).

fof(f930,plain,
    ( ~ v2_struct_0(sK2(sK2(sK2(sK0,sK1),sK12(sK1)),sK12(sK12(sK1))))
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))))
    | ~ spl22_110 ),
    inference(superposition,[],[f719,f916])).

fof(f956,plain,
    ( ~ spl22_115
    | ~ spl22_117
    | ~ spl22_119
    | spl22_97
    | ~ spl22_98
    | ~ spl22_110 ),
    inference(avatar_split_clause,[],[f937,f915,f854,f843,f954,f948,f942])).

fof(f942,plain,
    ( spl22_115
  <=> ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_115])])).

fof(f948,plain,
    ( spl22_117
  <=> ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_117])])).

fof(f954,plain,
    ( spl22_119
  <=> sK1 != sK12(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_119])])).

fof(f854,plain,
    ( spl22_98
  <=> v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_98])])).

fof(f937,plain,
    ( sK1 != sK12(sK1)
    | ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK1))
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK1),sK0)
    | ~ spl22_97
    | ~ spl22_98
    | ~ spl22_110 ),
    inference(inner_rewriting,[],[f936])).

fof(f936,plain,
    ( sK1 != sK12(sK1)
    | ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | ~ spl22_97
    | ~ spl22_98
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f935,f844])).

fof(f935,plain,
    ( sK1 != sK12(sK1)
    | ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_98
    | ~ spl22_110 ),
    inference(subsumption_resolution,[],[f925,f855])).

fof(f855,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_98 ),
    inference(avatar_component_clause,[],[f854])).

fof(f925,plain,
    ( sK1 != sK12(sK1)
    | ~ v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ v1_tdlat_3(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK0)
    | v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_110 ),
    inference(superposition,[],[f251,f916])).

fof(f923,plain,
    ( spl22_110
    | spl22_112
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f910,f812,f792,f716,f367,f921,f915])).

fof(f910,plain,
    ( v1_xboole_0(sK12(sK1))
    | u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) = sK12(sK1)
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f895,f368])).

fof(f895,plain,
    ( v1_xboole_0(sK12(sK1))
    | u1_struct_0(sK2(sK2(sK0,sK1),sK12(sK1))) = sK12(sK1)
    | v1_xboole_0(sK1)
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(resolution,[],[f834,f293])).

fof(f834,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | v1_xboole_0(X3)
        | u1_struct_0(sK2(sK2(sK0,sK1),X3)) = X3 )
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f833,f717])).

fof(f833,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK0,sK1))
        | u1_struct_0(sK2(sK2(sK0,sK1),X3)) = X3 )
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f820,f793])).

fof(f820,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK2(sK0,sK1))
        | v1_xboole_0(X3)
        | v2_struct_0(sK2(sK0,sK1))
        | u1_struct_0(sK2(sK2(sK0,sK1),X3)) = X3 )
    | ~ spl22_94 ),
    inference(superposition,[],[f262,f813])).

fof(f909,plain,
    ( spl22_106
    | spl22_108
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f894,f812,f792,f716,f907,f901])).

fof(f894,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK1)))
    | u1_struct_0(sK2(sK2(sK0,sK1),sK10(k1_zfmisc_1(sK1)))) = sK10(k1_zfmisc_1(sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(resolution,[],[f834,f289])).

fof(f890,plain,
    ( spl22_104
    | spl22_11
    | spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f883,f812,f792,f775,f716,f367,f888])).

fof(f883,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f882,f368])).

fof(f882,plain,
    ( v1_xboole_0(sK1)
    | v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f881,f813])).

fof(f881,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f880,f717])).

fof(f880,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_88
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f879,f776])).

fof(f879,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f825,f793])).

fof(f825,plain,
    ( v2_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_94 ),
    inference(superposition,[],[f799,f813])).

fof(f878,plain,
    ( spl22_102
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f871,f812,f792,f716,f367,f876])).

fof(f871,plain,
    ( l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f870,f368])).

fof(f870,plain,
    ( v1_xboole_0(sK1)
    | l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f869,f813])).

fof(f869,plain,
    ( l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f868,f717])).

fof(f868,plain,
    ( l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f824,f793])).

fof(f824,plain,
    ( l1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_94 ),
    inference(superposition,[],[f798,f813])).

fof(f867,plain,
    ( spl22_100
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f860,f812,f792,f716,f367,f865])).

fof(f865,plain,
    ( spl22_100
  <=> m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_100])])).

fof(f860,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f859,f368])).

fof(f859,plain,
    ( v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f858,f813])).

fof(f858,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f857,f793])).

fof(f857,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f823,f717])).

fof(f823,plain,
    ( m1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)),sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_94 ),
    inference(superposition,[],[f765,f813])).

fof(f856,plain,
    ( spl22_98
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f849,f812,f792,f716,f367,f854])).

fof(f849,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f848,f368])).

fof(f848,plain,
    ( v1_xboole_0(sK1)
    | v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f847,f813])).

fof(f847,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f846,f793])).

fof(f846,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f822,f717])).

fof(f822,plain,
    ( v1_pre_topc(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_94 ),
    inference(superposition,[],[f739,f813])).

fof(f845,plain,
    ( ~ spl22_97
    | spl22_11
    | spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(avatar_split_clause,[],[f838,f812,f792,f716,f367,f843])).

fof(f838,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_11
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f837,f368])).

fof(f837,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(forward_demodulation,[],[f836,f813])).

fof(f836,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_92
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f835,f793])).

fof(f835,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_83
    | ~ spl22_94 ),
    inference(subsumption_resolution,[],[f821,f717])).

fof(f821,plain,
    ( ~ v2_struct_0(sK2(sK2(sK0,sK1),sK12(sK1)))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl22_94 ),
    inference(superposition,[],[f719,f813])).

fof(f814,plain,
    ( spl22_94
    | ~ spl22_0
    | spl22_5
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f807,f367,f360,f346,f332,f812])).

fof(f807,plain,
    ( u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f806,f347])).

fof(f806,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f805,f368])).

fof(f805,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_0
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f801,f333])).

fof(f801,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK2(sK0,sK1)) = sK1
    | ~ spl22_8 ),
    inference(resolution,[],[f262,f361])).

fof(f794,plain,
    ( spl22_92
    | ~ spl22_0
    | ~ spl22_86 ),
    inference(avatar_split_clause,[],[f787,f762,f332,f792])).

fof(f787,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f768,f333])).

fof(f768,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_86 ),
    inference(resolution,[],[f763,f265])).

fof(f786,plain,
    ( spl22_88
    | ~ spl22_0
    | ~ spl22_2
    | ~ spl22_86 ),
    inference(avatar_split_clause,[],[f785,f762,f339,f332,f775])).

fof(f339,plain,
    ( spl22_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_2])])).

fof(f785,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_2
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f784,f340])).

fof(f340,plain,
    ( v2_pre_topc(sK0)
    | ~ spl22_2 ),
    inference(avatar_component_clause,[],[f339])).

fof(f784,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f767,f333])).

fof(f767,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_86 ),
    inference(resolution,[],[f763,f263])).

fof(f783,plain,
    ( spl22_88
    | ~ spl22_91
    | ~ spl22_0
    | spl22_5
    | ~ spl22_86 ),
    inference(avatar_split_clause,[],[f770,f762,f346,f332,f781,f775])).

fof(f770,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f769,f347])).

fof(f769,plain,
    ( v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_86 ),
    inference(subsumption_resolution,[],[f766,f333])).

fof(f766,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl22_86 ),
    inference(resolution,[],[f763,f266])).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f231])).

fof(f231,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f230])).

fof(f230,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',cc14_tex_2)).

fof(f764,plain,
    ( spl22_86
    | ~ spl22_0
    | spl22_5
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f757,f367,f360,f346,f332,f762])).

fof(f757,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f756,f347])).

fof(f756,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f755,f368])).

fof(f755,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_0
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f751,f333])).

fof(f751,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl22_8 ),
    inference(resolution,[],[f261,f361])).

fof(f738,plain,
    ( spl22_84
    | ~ spl22_0
    | spl22_5
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f731,f367,f360,f346,f332,f736])).

fof(f731,plain,
    ( v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f730,f347])).

fof(f730,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f729,f368])).

fof(f729,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f725,f333])).

fof(f725,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | v1_pre_topc(sK2(sK0,sK1))
    | ~ spl22_8 ),
    inference(resolution,[],[f260,f361])).

fof(f718,plain,
    ( ~ spl22_83
    | ~ spl22_0
    | spl22_5
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f711,f367,f360,f346,f332,f716])).

fof(f711,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f710,f347])).

fof(f710,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f709,f368])).

fof(f709,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_0
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f705,f333])).

fof(f705,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl22_8 ),
    inference(resolution,[],[f259,f361])).

fof(f665,plain,
    ( spl22_78
    | ~ spl22_81
    | ~ spl22_48
    | spl22_51
    | ~ spl22_52 ),
    inference(avatar_split_clause,[],[f652,f514,f507,f500,f663,f657])).

fof(f657,plain,
    ( spl22_78
  <=> v1_tdlat_3(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_78])])).

fof(f663,plain,
    ( spl22_81
  <=> ~ v2_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_81])])).

fof(f500,plain,
    ( spl22_48
  <=> v7_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_48])])).

fof(f507,plain,
    ( spl22_51
  <=> ~ v2_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_51])])).

fof(f514,plain,
    ( spl22_52
  <=> l1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_52])])).

fof(f652,plain,
    ( ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ spl22_48
    | ~ spl22_51
    | ~ spl22_52 ),
    inference(subsumption_resolution,[],[f651,f515])).

fof(f515,plain,
    ( l1_pre_topc(sK17)
    | ~ spl22_52 ),
    inference(avatar_component_clause,[],[f514])).

fof(f651,plain,
    ( ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ l1_pre_topc(sK17)
    | ~ spl22_48
    | ~ spl22_51 ),
    inference(subsumption_resolution,[],[f638,f508])).

fof(f508,plain,
    ( ~ v2_struct_0(sK17)
    | ~ spl22_51 ),
    inference(avatar_component_clause,[],[f507])).

fof(f638,plain,
    ( v2_struct_0(sK17)
    | ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ l1_pre_topc(sK17)
    | ~ spl22_48 ),
    inference(resolution,[],[f268,f501])).

fof(f501,plain,
    ( v7_struct_0(sK17)
    | ~ spl22_48 ),
    inference(avatar_component_clause,[],[f500])).

fof(f268,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f235])).

fof(f235,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f234])).

fof(f234,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',cc3_tex_1)).

fof(f650,plain,
    ( spl22_76
    | ~ spl22_36
    | ~ spl22_40
    | spl22_43
    | ~ spl22_44 ),
    inference(avatar_split_clause,[],[f643,f486,f479,f472,f458,f648])).

fof(f648,plain,
    ( spl22_76
  <=> v1_tdlat_3(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_76])])).

fof(f458,plain,
    ( spl22_36
  <=> v2_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_36])])).

fof(f472,plain,
    ( spl22_40
  <=> v7_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_40])])).

fof(f479,plain,
    ( spl22_43
  <=> ~ v2_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_43])])).

fof(f486,plain,
    ( spl22_44
  <=> l1_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_44])])).

fof(f643,plain,
    ( v1_tdlat_3(sK16)
    | ~ spl22_36
    | ~ spl22_40
    | ~ spl22_43
    | ~ spl22_44 ),
    inference(subsumption_resolution,[],[f642,f487])).

fof(f487,plain,
    ( l1_pre_topc(sK16)
    | ~ spl22_44 ),
    inference(avatar_component_clause,[],[f486])).

fof(f642,plain,
    ( v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl22_36
    | ~ spl22_40
    | ~ spl22_43 ),
    inference(subsumption_resolution,[],[f641,f459])).

fof(f459,plain,
    ( v2_pre_topc(sK16)
    | ~ spl22_36 ),
    inference(avatar_component_clause,[],[f458])).

fof(f641,plain,
    ( ~ v2_pre_topc(sK16)
    | v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl22_40
    | ~ spl22_43 ),
    inference(subsumption_resolution,[],[f637,f480])).

fof(f480,plain,
    ( ~ v2_struct_0(sK16)
    | ~ spl22_43 ),
    inference(avatar_component_clause,[],[f479])).

fof(f637,plain,
    ( v2_struct_0(sK16)
    | ~ v2_pre_topc(sK16)
    | v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl22_40 ),
    inference(resolution,[],[f268,f473])).

fof(f473,plain,
    ( v7_struct_0(sK16)
    | ~ spl22_40 ),
    inference(avatar_component_clause,[],[f472])).

fof(f625,plain,
    ( spl22_74
    | ~ spl22_30 ),
    inference(avatar_split_clause,[],[f617,f437,f623])).

fof(f623,plain,
    ( spl22_74
  <=> sK10(k1_zfmisc_1(sK13)) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_74])])).

fof(f617,plain,
    ( sK10(k1_zfmisc_1(sK13)) = sK13
    | ~ spl22_30 ),
    inference(resolution,[],[f607,f438])).

fof(f606,plain,
    ( ~ spl22_73
    | ~ spl22_8
    | spl22_11 ),
    inference(avatar_split_clause,[],[f599,f367,f360,f604])).

fof(f604,plain,
    ( spl22_73
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_73])])).

fof(f599,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl22_8
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f595,f368])).

fof(f595,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl22_8 ),
    inference(resolution,[],[f292,f361])).

fof(f579,plain,(
    spl22_70 ),
    inference(avatar_split_clause,[],[f313,f577])).

fof(f577,plain,
    ( spl22_70
  <=> l1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_70])])).

fof(f313,plain,(
    l1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f165])).

fof(f165,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc2_tex_1)).

fof(f572,plain,(
    ~ spl22_69 ),
    inference(avatar_split_clause,[],[f314,f570])).

fof(f570,plain,
    ( spl22_69
  <=> ~ v2_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_69])])).

fof(f314,plain,(
    ~ v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f165])).

fof(f565,plain,(
    ~ spl22_67 ),
    inference(avatar_split_clause,[],[f315,f563])).

fof(f563,plain,
    ( spl22_67
  <=> ~ v7_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_67])])).

fof(f315,plain,(
    ~ v7_struct_0(sK19) ),
    inference(cnf_transformation,[],[f165])).

fof(f558,plain,(
    spl22_64 ),
    inference(avatar_split_clause,[],[f316,f556])).

fof(f556,plain,
    ( spl22_64
  <=> v1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_64])])).

fof(f316,plain,(
    v1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f165])).

fof(f551,plain,(
    spl22_62 ),
    inference(avatar_split_clause,[],[f308,f549])).

fof(f549,plain,
    ( spl22_62
  <=> l1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_62])])).

fof(f308,plain,(
    l1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f184])).

fof(f184,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc4_tex_1)).

fof(f544,plain,(
    ~ spl22_61 ),
    inference(avatar_split_clause,[],[f309,f542])).

fof(f542,plain,
    ( spl22_61
  <=> ~ v2_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_61])])).

fof(f309,plain,(
    ~ v2_struct_0(sK18) ),
    inference(cnf_transformation,[],[f184])).

fof(f537,plain,(
    ~ spl22_59 ),
    inference(avatar_split_clause,[],[f310,f535])).

fof(f535,plain,
    ( spl22_59
  <=> ~ v7_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_59])])).

fof(f310,plain,(
    ~ v7_struct_0(sK18) ),
    inference(cnf_transformation,[],[f184])).

fof(f530,plain,(
    spl22_56 ),
    inference(avatar_split_clause,[],[f311,f528])).

fof(f528,plain,
    ( spl22_56
  <=> v1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_56])])).

fof(f311,plain,(
    v1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f184])).

fof(f523,plain,(
    spl22_54 ),
    inference(avatar_split_clause,[],[f312,f521])).

fof(f521,plain,
    ( spl22_54
  <=> v2_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_54])])).

fof(f312,plain,(
    v2_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f184])).

fof(f516,plain,(
    spl22_52 ),
    inference(avatar_split_clause,[],[f304,f514])).

fof(f304,plain,(
    l1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f152])).

fof(f152,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc1_tex_1)).

fof(f509,plain,(
    ~ spl22_51 ),
    inference(avatar_split_clause,[],[f305,f507])).

fof(f305,plain,(
    ~ v2_struct_0(sK17) ),
    inference(cnf_transformation,[],[f152])).

fof(f502,plain,(
    spl22_48 ),
    inference(avatar_split_clause,[],[f306,f500])).

fof(f306,plain,(
    v7_struct_0(sK17) ),
    inference(cnf_transformation,[],[f152])).

fof(f495,plain,(
    spl22_46 ),
    inference(avatar_split_clause,[],[f307,f493])).

fof(f493,plain,
    ( spl22_46
  <=> v1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_46])])).

fof(f307,plain,(
    v1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f152])).

fof(f488,plain,(
    spl22_44 ),
    inference(avatar_split_clause,[],[f299,f486])).

fof(f299,plain,(
    l1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc3_tex_1)).

fof(f481,plain,(
    ~ spl22_43 ),
    inference(avatar_split_clause,[],[f300,f479])).

fof(f300,plain,(
    ~ v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f175])).

fof(f474,plain,(
    spl22_40 ),
    inference(avatar_split_clause,[],[f301,f472])).

fof(f301,plain,(
    v7_struct_0(sK16) ),
    inference(cnf_transformation,[],[f175])).

fof(f467,plain,(
    spl22_38 ),
    inference(avatar_split_clause,[],[f302,f465])).

fof(f465,plain,
    ( spl22_38
  <=> v1_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_38])])).

fof(f302,plain,(
    v1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f175])).

fof(f460,plain,(
    spl22_36 ),
    inference(avatar_split_clause,[],[f303,f458])).

fof(f303,plain,(
    v2_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f175])).

fof(f453,plain,(
    spl22_34 ),
    inference(avatar_split_clause,[],[f298,f451])).

fof(f451,plain,
    ( spl22_34
  <=> l1_pre_topc(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_34])])).

fof(f298,plain,(
    l1_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',existence_l1_pre_topc)).

fof(f446,plain,(
    ~ spl22_33 ),
    inference(avatar_split_clause,[],[f297,f444])).

fof(f444,plain,
    ( spl22_33
  <=> ~ v1_xboole_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_33])])).

fof(f297,plain,(
    ~ v1_xboole_0(sK14) ),
    inference(cnf_transformation,[],[f168])).

fof(f168,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc2_xboole_0)).

fof(f439,plain,(
    spl22_30 ),
    inference(avatar_split_clause,[],[f296,f437])).

fof(f296,plain,(
    v1_xboole_0(sK13) ),
    inference(cnf_transformation,[],[f155])).

fof(f155,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc1_xboole_0)).

fof(f432,plain,(
    spl22_28 ),
    inference(avatar_split_clause,[],[f275,f430])).

fof(f430,plain,
    ( spl22_28
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_28])])).

fof(f275,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f160])).

fof(f160,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc2_pre_topc)).

fof(f425,plain,(
    ~ spl22_27 ),
    inference(avatar_split_clause,[],[f276,f423])).

fof(f423,plain,
    ( spl22_27
  <=> ~ v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_27])])).

fof(f276,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f160])).

fof(f418,plain,(
    spl22_24 ),
    inference(avatar_split_clause,[],[f277,f416])).

fof(f416,plain,
    ( spl22_24
  <=> v1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_24])])).

fof(f277,plain,(
    v1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f160])).

fof(f411,plain,(
    spl22_22 ),
    inference(avatar_split_clause,[],[f278,f409])).

fof(f409,plain,
    ( spl22_22
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_22])])).

fof(f278,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f160])).

fof(f404,plain,(
    spl22_20 ),
    inference(avatar_split_clause,[],[f273,f402])).

fof(f402,plain,
    ( spl22_20
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_20])])).

fof(f273,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc1_pre_topc)).

fof(f397,plain,(
    spl22_18 ),
    inference(avatar_split_clause,[],[f274,f395])).

fof(f395,plain,
    ( spl22_18
  <=> v1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_18])])).

fof(f274,plain,(
    v1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f147])).

fof(f390,plain,(
    spl22_16 ),
    inference(avatar_split_clause,[],[f270,f388])).

fof(f388,plain,
    ( spl22_16
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_16])])).

fof(f270,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t34_tex_2.p',rc11_pre_topc)).

fof(f383,plain,(
    spl22_14 ),
    inference(avatar_split_clause,[],[f271,f381])).

fof(f381,plain,
    ( spl22_14
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_14])])).

fof(f271,plain,(
    v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f137])).

fof(f376,plain,(
    spl22_12 ),
    inference(avatar_split_clause,[],[f272,f374])).

fof(f374,plain,
    ( spl22_12
  <=> v1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_12])])).

fof(f272,plain,(
    v1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f137])).

fof(f369,plain,(
    ~ spl22_11 ),
    inference(avatar_split_clause,[],[f252,f367])).

fof(f252,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f222])).

fof(f362,plain,(
    spl22_8 ),
    inference(avatar_split_clause,[],[f253,f360])).

fof(f253,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f222])).

fof(f355,plain,(
    spl22_6 ),
    inference(avatar_split_clause,[],[f254,f353])).

fof(f254,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f222])).

fof(f348,plain,(
    ~ spl22_5 ),
    inference(avatar_split_clause,[],[f255,f346])).

fof(f255,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f222])).

fof(f341,plain,(
    spl22_2 ),
    inference(avatar_split_clause,[],[f256,f339])).

fof(f256,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f222])).

fof(f334,plain,(
    spl22_0 ),
    inference(avatar_split_clause,[],[f257,f332])).

fof(f257,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f222])).
%------------------------------------------------------------------------------
