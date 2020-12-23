%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 176 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :    9
%              Number of atoms          :  349 ( 597 expanded)
%              Number of equality atoms :   55 (  92 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1379,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f98,f169,f194,f206,f210,f250,f266,f297,f373,f1072,f1200,f1332,f1371])).

fof(f1371,plain,
    ( ~ spl2_2
    | spl2_4
    | ~ spl2_5
    | ~ spl2_19
    | ~ spl2_29
    | ~ spl2_31
    | ~ spl2_39
    | ~ spl2_71
    | ~ spl2_80
    | ~ spl2_86 ),
    inference(avatar_contradiction_clause,[],[f1370])).

fof(f1370,plain,
    ( $false
    | ~ spl2_2
    | spl2_4
    | ~ spl2_5
    | ~ spl2_19
    | ~ spl2_29
    | ~ spl2_31
    | ~ spl2_39
    | ~ spl2_71
    | ~ spl2_80
    | ~ spl2_86 ),
    inference(subsumption_resolution,[],[f93,f1369])).

fof(f1369,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_19
    | ~ spl2_29
    | ~ spl2_31
    | ~ spl2_39
    | ~ spl2_71
    | ~ spl2_80
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f1368,f97])).

fof(f97,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1368,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_19
    | ~ spl2_29
    | ~ spl2_31
    | ~ spl2_39
    | ~ spl2_71
    | ~ spl2_80
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f1367,f1356])).

fof(f1356,plain,
    ( ! [X0] : k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
    | ~ spl2_19
    | ~ spl2_86 ),
    inference(unit_resulting_resolution,[],[f1331,f168])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f1331,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_86 ),
    inference(avatar_component_clause,[],[f1329])).

fof(f1329,plain,
    ( spl2_86
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f1367,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_29
    | ~ spl2_31
    | ~ spl2_39
    | ~ spl2_71
    | ~ spl2_80
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f1366,f1201])).

fof(f1201,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_31
    | ~ spl2_71
    | ~ spl2_80 ),
    inference(unit_resulting_resolution,[],[f83,f296,f1199,f1071])).

fof(f1071,plain,
    ( ! [X4,X5] :
        ( k2_tops_1(X4,X5) = k2_pre_topc(X4,k2_tops_1(X4,X5))
        | ~ v4_pre_topc(k2_tops_1(X4,X5),X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) )
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1070,plain,
    ( spl2_71
  <=> ! [X5,X4] :
        ( ~ v4_pre_topc(k2_tops_1(X4,X5),X4)
        | k2_tops_1(X4,X5) = k2_pre_topc(X4,k2_tops_1(X4,X5))
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f1199,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f1197,plain,
    ( spl2_80
  <=> v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f296,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl2_31
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f83,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1366,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_29
    | ~ spl2_39
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f1346,f372])).

fof(f372,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl2_39
  <=> k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f1346,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_2
    | ~ spl2_29
    | ~ spl2_86 ),
    inference(unit_resulting_resolution,[],[f83,f1331,f265])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl2_29
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f93,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_4
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1332,plain,
    ( spl2_86
    | ~ spl2_2
    | ~ spl2_22
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f300,f294,f204,f81,f1329])).

fof(f204,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f300,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_22
    | ~ spl2_31 ),
    inference(unit_resulting_resolution,[],[f83,f296,f205])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f1200,plain,
    ( spl2_80
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f298,f294,f192,f81,f76,f1197])).

fof(f76,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f192,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f298,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20
    | ~ spl2_31 ),
    inference(unit_resulting_resolution,[],[f78,f83,f296,f193])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k2_tops_1(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f192])).

fof(f78,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f1072,plain,
    ( spl2_71
    | ~ spl2_22
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f230,f208,f204,f1070])).

fof(f208,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f230,plain,
    ( ! [X4,X5] :
        ( ~ v4_pre_topc(k2_tops_1(X4,X5),X4)
        | k2_tops_1(X4,X5) = k2_pre_topc(X4,k2_tops_1(X4,X5))
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) )
    | ~ spl2_22
    | ~ spl2_23 ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( ! [X4,X5] :
        ( ~ v4_pre_topc(k2_tops_1(X4,X5),X4)
        | k2_tops_1(X4,X5) = k2_pre_topc(X4,k2_tops_1(X4,X5))
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
    | ~ spl2_22
    | ~ spl2_23 ),
    inference(resolution,[],[f209,f205])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f208])).

fof(f373,plain,
    ( spl2_39
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f260,f248,f86,f81,f76,f370])).

fof(f86,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f248,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f260,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f78,f83,f88,f249])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f248])).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f297,plain,
    ( spl2_31
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f218,f204,f86,f81,f294])).

fof(f218,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f83,f88,f205])).

fof(f266,plain,(
    spl2_29 ),
    inference(avatar_split_clause,[],[f56,f264])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f250,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f60,f248])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

fof(f210,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f57,f208])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f206,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f69,f204])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f194,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f67,f192])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_tops_1)).

fof(f169,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f73,f167])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f98,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f53,f96])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f94,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f52,f91])).

fof(f52,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

fof(f89,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f51,f86])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f50,f81])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f49,f76])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (19817)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.41  % (19809)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (19811)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (19818)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (19821)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (19813)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (19806)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (19810)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (19808)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (19816)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (19820)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (19814)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (19807)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (19812)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (19822)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (19823)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (19811)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1379,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f98,f169,f194,f206,f210,f250,f266,f297,f373,f1072,f1200,f1332,f1371])).
% 0.21/0.50  fof(f1371,plain,(
% 0.21/0.50    ~spl2_2 | spl2_4 | ~spl2_5 | ~spl2_19 | ~spl2_29 | ~spl2_31 | ~spl2_39 | ~spl2_71 | ~spl2_80 | ~spl2_86),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1370])).
% 0.21/0.50  fof(f1370,plain,(
% 0.21/0.50    $false | (~spl2_2 | spl2_4 | ~spl2_5 | ~spl2_19 | ~spl2_29 | ~spl2_31 | ~spl2_39 | ~spl2_71 | ~spl2_80 | ~spl2_86)),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f1369])).
% 0.21/0.50  fof(f1369,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_5 | ~spl2_19 | ~spl2_29 | ~spl2_31 | ~spl2_39 | ~spl2_71 | ~spl2_80 | ~spl2_86)),
% 0.21/0.50    inference(forward_demodulation,[],[f1368,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl2_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.50  fof(f1368,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | (~spl2_2 | ~spl2_19 | ~spl2_29 | ~spl2_31 | ~spl2_39 | ~spl2_71 | ~spl2_80 | ~spl2_86)),
% 0.21/0.50    inference(forward_demodulation,[],[f1367,f1356])).
% 0.21/0.50  fof(f1356,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)) ) | (~spl2_19 | ~spl2_86)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f1331,f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl2_19 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.50  fof(f1331,plain,(
% 0.21/0.50    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_86),
% 0.21/0.50    inference(avatar_component_clause,[],[f1329])).
% 0.21/0.50  fof(f1329,plain,(
% 0.21/0.50    spl2_86 <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 0.21/0.50  fof(f1367,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | (~spl2_2 | ~spl2_29 | ~spl2_31 | ~spl2_39 | ~spl2_71 | ~spl2_80 | ~spl2_86)),
% 0.21/0.50    inference(forward_demodulation,[],[f1366,f1201])).
% 0.21/0.50  fof(f1201,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_31 | ~spl2_71 | ~spl2_80)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f83,f296,f1199,f1071])).
% 0.21/0.50  fof(f1071,plain,(
% 0.21/0.50    ( ! [X4,X5] : (k2_tops_1(X4,X5) = k2_pre_topc(X4,k2_tops_1(X4,X5)) | ~v4_pre_topc(k2_tops_1(X4,X5),X4) | ~l1_pre_topc(X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))) ) | ~spl2_71),
% 0.21/0.50    inference(avatar_component_clause,[],[f1070])).
% 0.21/0.50  fof(f1070,plain,(
% 0.21/0.50    spl2_71 <=> ! [X5,X4] : (~v4_pre_topc(k2_tops_1(X4,X5),X4) | k2_tops_1(X4,X5) = k2_pre_topc(X4,k2_tops_1(X4,X5)) | ~l1_pre_topc(X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.21/0.50  fof(f1199,plain,(
% 0.21/0.50    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~spl2_80),
% 0.21/0.50    inference(avatar_component_clause,[],[f1197])).
% 0.21/0.50  fof(f1197,plain,(
% 0.21/0.50    spl2_80 <=> v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f294])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    spl2_31 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f1366,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) | (~spl2_2 | ~spl2_29 | ~spl2_39 | ~spl2_86)),
% 0.21/0.50    inference(forward_demodulation,[],[f1346,f372])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~spl2_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f370])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    spl2_39 <=> k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.50  fof(f1346,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | (~spl2_2 | ~spl2_29 | ~spl2_86)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f83,f1331,f265])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f264])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    spl2_29 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl2_4 <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f1332,plain,(
% 0.21/0.50    spl2_86 | ~spl2_2 | ~spl2_22 | ~spl2_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f300,f294,f204,f81,f1329])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl2_22 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_22 | ~spl2_31)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f83,f296,f205])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f204])).
% 0.21/0.50  fof(f1200,plain,(
% 0.21/0.50    spl2_80 | ~spl2_1 | ~spl2_2 | ~spl2_20 | ~spl2_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f298,f294,f192,f81,f76,f1197])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    spl2_20 <=> ! [X1,X0] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_20 | ~spl2_31)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f78,f83,f296,f193])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f192])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f1072,plain,(
% 0.21/0.50    spl2_71 | ~spl2_22 | ~spl2_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f230,f208,f204,f1070])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    spl2_23 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ( ! [X4,X5] : (~v4_pre_topc(k2_tops_1(X4,X5),X4) | k2_tops_1(X4,X5) = k2_pre_topc(X4,k2_tops_1(X4,X5)) | ~l1_pre_topc(X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))) ) | (~spl2_22 | ~spl2_23)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f228])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ( ! [X4,X5] : (~v4_pre_topc(k2_tops_1(X4,X5),X4) | k2_tops_1(X4,X5) = k2_pre_topc(X4,k2_tops_1(X4,X5)) | ~l1_pre_topc(X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4)) ) | (~spl2_22 | ~spl2_23)),
% 0.21/0.50    inference(resolution,[],[f209,f205])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) ) | ~spl2_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f208])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    spl2_39 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f260,f248,f86,f81,f76,f370])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    spl2_28 <=> ! [X1,X0] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_28)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f78,f83,f88,f249])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f248])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f86])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    spl2_31 | ~spl2_2 | ~spl2_3 | ~spl2_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f218,f204,f86,f81,f294])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_22)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f83,f88,f205])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    spl2_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f264])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    spl2_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f248])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    spl2_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f208])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    spl2_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f204])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    spl2_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f67,f192])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_tops_1(X0,X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_tops_1)).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl2_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f167])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl2_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f96])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ~spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f91])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f46,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f21])).
% 0.21/0.51  fof(f21,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f86])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f81])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f76])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (19811)------------------------------
% 0.21/0.51  % (19811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19811)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (19811)Memory used [KB]: 7164
% 0.21/0.51  % (19811)Time elapsed: 0.108 s
% 0.21/0.51  % (19811)------------------------------
% 0.21/0.51  % (19811)------------------------------
% 0.21/0.51  % (19805)Success in time 0.155 s
%------------------------------------------------------------------------------
