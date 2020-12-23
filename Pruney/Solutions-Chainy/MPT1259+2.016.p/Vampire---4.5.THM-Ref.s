%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 237 expanded)
%              Number of leaves         :   35 ( 105 expanded)
%              Depth                    :    7
%              Number of atoms          :  448 ( 740 expanded)
%              Number of equality atoms :   87 ( 145 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f378,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f62,f66,f71,f75,f79,f83,f93,f102,f109,f116,f141,f150,f167,f179,f237,f248,f257,f337,f363,f372,f377])).

fof(f377,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_47
    | ~ spl2_49 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_47
    | ~ spl2_49 ),
    inference(subsumption_resolution,[],[f375,f70])).

fof(f70,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f375,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_47
    | ~ spl2_49 ),
    inference(backward_demodulation,[],[f362,f374])).

fof(f374,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_49 ),
    inference(forward_demodulation,[],[f373,f65])).

fof(f65,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_5
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f373,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_49 ),
    inference(superposition,[],[f371,f61])).

fof(f61,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_4
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f371,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl2_49
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f362,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl2_47
  <=> k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f372,plain,
    ( spl2_49
    | ~ spl2_9
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f171,f156,f81,f370])).

fof(f81,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f156,plain,
    ( spl2_20
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f171,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))
    | ~ spl2_9
    | ~ spl2_20 ),
    inference(resolution,[],[f157,f82])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f157,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f156])).

fof(f363,plain,
    ( spl2_47
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_31
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f345,f335,f245,f156,f147,f360])).

fof(f147,plain,
    ( spl2_19
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f245,plain,
    ( spl2_31
  <=> k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f335,plain,
    ( spl2_44
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f345,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_31
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f344,f149])).

fof(f149,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f344,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)
    | ~ spl2_20
    | ~ spl2_31
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f340,f247])).

fof(f247,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f245])).

fof(f340,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_20
    | ~ spl2_44 ),
    inference(resolution,[],[f336,f157])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f335])).

fof(f337,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f333,f255,f50,f335])).

fof(f50,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f255,plain,
    ( spl2_33
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_33 ),
    inference(resolution,[],[f256,f52])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,(
    spl2_33 ),
    inference(avatar_split_clause,[],[f33,f255])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f248,plain,
    ( spl2_31
    | ~ spl2_3
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f238,f235,f55,f245])).

fof(f55,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f235,plain,
    ( spl2_30
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f238,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_30 ),
    inference(resolution,[],[f236,f57])).

fof(f57,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) )
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f235])).

fof(f237,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f233,f177,f50,f45,f235])).

fof(f45,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f177,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f232,f52])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) )
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f178,f47])).

fof(f47,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f36,f177])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

fof(f167,plain,
    ( ~ spl2_2
    | ~ spl2_8
    | ~ spl2_17
    | spl2_20 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_17
    | spl2_20 ),
    inference(subsumption_resolution,[],[f165,f52])).

fof(f165,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_8
    | ~ spl2_17
    | spl2_20 ),
    inference(subsumption_resolution,[],[f164,f131])).

fof(f131,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_17
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f164,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_8
    | spl2_20 ),
    inference(resolution,[],[f158,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f158,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f156])).

fof(f150,plain,
    ( spl2_19
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f144,f130,f114,f147])).

fof(f114,plain,
    ( spl2_15
  <=> ! [X0] :
        ( k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f144,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(resolution,[],[f131,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f141,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8
    | spl2_17 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8
    | spl2_17 ),
    inference(subsumption_resolution,[],[f139,f52])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_8
    | spl2_17 ),
    inference(subsumption_resolution,[],[f138,f57])).

fof(f138,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_8
    | spl2_17 ),
    inference(resolution,[],[f132,f78])).

fof(f132,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f130])).

fof(f116,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f112,f107,f77,f50,f114])).

fof(f107,plain,
    ( spl2_14
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f112,plain,
    ( ! [X0] :
        ( k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f111,f52])).

fof(f111,plain,
    ( ! [X0] :
        ( k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( ! [X0] :
        ( k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(resolution,[],[f108,f78])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f107])).

fof(f109,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f105,f100,f73,f50,f45,f107])).

fof(f73,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f100,plain,
    ( spl2_13
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f104,f47])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f103,f52])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(resolution,[],[f101,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k2_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f94,f91,f50,f100])).

fof(f91,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f92,f52])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f34,f91])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f83,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f42,f81])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f79,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f75,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).

fof(f71,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
    ( ? [X1] :
        ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

fof(f66,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f43,f64])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f41,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (18894)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (18894)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f378,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f48,f53,f58,f62,f66,f71,f75,f79,f83,f93,f102,f109,f116,f141,f150,f167,f179,f237,f248,f257,f337,f363,f372,f377])).
% 0.21/0.44  fof(f377,plain,(
% 0.21/0.44    ~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_47 | ~spl2_49),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f376])).
% 0.21/0.44  fof(f376,plain,(
% 0.21/0.44    $false | (~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_47 | ~spl2_49)),
% 0.21/0.44    inference(subsumption_resolution,[],[f375,f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | spl2_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl2_6 <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f375,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_5 | ~spl2_47 | ~spl2_49)),
% 0.21/0.44    inference(backward_demodulation,[],[f362,f374])).
% 0.21/0.44  fof(f374,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | (~spl2_4 | ~spl2_5 | ~spl2_49)),
% 0.21/0.44    inference(forward_demodulation,[],[f373,f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl2_5 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f373,plain,(
% 0.21/0.44    k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | (~spl2_4 | ~spl2_49)),
% 0.21/0.44    inference(superposition,[],[f371,f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl2_4 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f371,plain,(
% 0.21/0.44    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))) ) | ~spl2_49),
% 0.21/0.44    inference(avatar_component_clause,[],[f370])).
% 0.21/0.44  fof(f370,plain,(
% 0.21/0.44    spl2_49 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.44  fof(f362,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | ~spl2_47),
% 0.21/0.44    inference(avatar_component_clause,[],[f360])).
% 0.21/0.44  fof(f360,plain,(
% 0.21/0.44    spl2_47 <=> k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.21/0.44  fof(f372,plain,(
% 0.21/0.44    spl2_49 | ~spl2_9 | ~spl2_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f171,f156,f81,f370])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    spl2_9 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    spl2_20 <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))) ) | (~spl2_9 | ~spl2_20)),
% 0.21/0.44    inference(resolution,[],[f157,f82])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f81])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f156])).
% 0.21/0.44  fof(f363,plain,(
% 0.21/0.44    spl2_47 | ~spl2_19 | ~spl2_20 | ~spl2_31 | ~spl2_44),
% 0.21/0.44    inference(avatar_split_clause,[],[f345,f335,f245,f156,f147,f360])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    spl2_19 <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.44  fof(f245,plain,(
% 0.21/0.44    spl2_31 <=> k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.44  fof(f335,plain,(
% 0.21/0.44    spl2_44 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.44  fof(f345,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | (~spl2_19 | ~spl2_20 | ~spl2_31 | ~spl2_44)),
% 0.21/0.44    inference(forward_demodulation,[],[f344,f149])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~spl2_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f147])).
% 0.21/0.44  fof(f344,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) | (~spl2_20 | ~spl2_31 | ~spl2_44)),
% 0.21/0.44    inference(forward_demodulation,[],[f340,f247])).
% 0.21/0.44  fof(f247,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~spl2_31),
% 0.21/0.44    inference(avatar_component_clause,[],[f245])).
% 0.21/0.44  fof(f340,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | (~spl2_20 | ~spl2_44)),
% 0.21/0.44    inference(resolution,[],[f336,f157])).
% 0.21/0.44  fof(f336,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_44),
% 0.21/0.44    inference(avatar_component_clause,[],[f335])).
% 0.21/0.44  fof(f337,plain,(
% 0.21/0.44    spl2_44 | ~spl2_2 | ~spl2_33),
% 0.21/0.44    inference(avatar_split_clause,[],[f333,f255,f50,f335])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f255,plain,(
% 0.21/0.44    spl2_33 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.44  fof(f333,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_33)),
% 0.21/0.44    inference(resolution,[],[f256,f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f50])).
% 0.21/0.44  fof(f256,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) ) | ~spl2_33),
% 0.21/0.44    inference(avatar_component_clause,[],[f255])).
% 0.21/0.44  fof(f257,plain,(
% 0.21/0.44    spl2_33),
% 0.21/0.44    inference(avatar_split_clause,[],[f33,f255])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.44  fof(f248,plain,(
% 0.21/0.44    spl2_31 | ~spl2_3 | ~spl2_30),
% 0.21/0.44    inference(avatar_split_clause,[],[f238,f235,f55,f245])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f235,plain,(
% 0.21/0.44    spl2_30 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.44  fof(f238,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_30)),
% 0.21/0.44    inference(resolution,[],[f236,f57])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f55])).
% 0.21/0.44  fof(f236,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) ) | ~spl2_30),
% 0.21/0.44    inference(avatar_component_clause,[],[f235])).
% 0.21/0.44  fof(f237,plain,(
% 0.21/0.44    spl2_30 | ~spl2_1 | ~spl2_2 | ~spl2_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f233,f177,f50,f45,f235])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f177,plain,(
% 0.21/0.44    spl2_23 <=> ! [X1,X0] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.44  fof(f233,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_23)),
% 0.21/0.44    inference(subsumption_resolution,[],[f232,f52])).
% 0.21/0.44  fof(f232,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) ) | (~spl2_1 | ~spl2_23)),
% 0.21/0.44    inference(resolution,[],[f178,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f178,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))) ) | ~spl2_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f177])).
% 0.21/0.44  fof(f179,plain,(
% 0.21/0.44    spl2_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f36,f177])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).
% 0.21/0.44  fof(f167,plain,(
% 0.21/0.44    ~spl2_2 | ~spl2_8 | ~spl2_17 | spl2_20),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    $false | (~spl2_2 | ~spl2_8 | ~spl2_17 | spl2_20)),
% 0.21/0.44    inference(subsumption_resolution,[],[f165,f52])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | (~spl2_8 | ~spl2_17 | spl2_20)),
% 0.21/0.44    inference(subsumption_resolution,[],[f164,f131])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f130])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    spl2_17 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_8 | spl2_20)),
% 0.21/0.44    inference(resolution,[],[f158,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f77])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl2_8 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f156])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    spl2_19 | ~spl2_15 | ~spl2_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f144,f130,f114,f147])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    spl2_15 <=> ! [X0] : (k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_15 | ~spl2_17)),
% 0.21/0.44    inference(resolution,[],[f131,f115])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))) ) | ~spl2_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f114])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    ~spl2_2 | ~spl2_3 | ~spl2_8 | spl2_17),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    $false | (~spl2_2 | ~spl2_3 | ~spl2_8 | spl2_17)),
% 0.21/0.44    inference(subsumption_resolution,[],[f139,f52])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_8 | spl2_17)),
% 0.21/0.44    inference(subsumption_resolution,[],[f138,f57])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_8 | spl2_17)),
% 0.21/0.44    inference(resolution,[],[f132,f78])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f130])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    spl2_15 | ~spl2_2 | ~spl2_8 | ~spl2_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f112,f107,f77,f50,f114])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    spl2_14 <=> ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_8 | ~spl2_14)),
% 0.21/0.44    inference(subsumption_resolution,[],[f111,f52])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_8 | ~spl2_14)),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f110])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_8 | ~spl2_14)),
% 0.21/0.44    inference(resolution,[],[f108,f78])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f107])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl2_14 | ~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f105,f100,f73,f50,f45,f107])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    spl2_7 <=> ! [X1,X0] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    spl2_13 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_13)),
% 0.21/0.44    inference(subsumption_resolution,[],[f104,f47])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) ) | (~spl2_2 | ~spl2_7 | ~spl2_13)),
% 0.21/0.44    inference(subsumption_resolution,[],[f103,f52])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl2_7 | ~spl2_13)),
% 0.21/0.44    inference(resolution,[],[f101,f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f73])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f100])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    spl2_13 | ~spl2_2 | ~spl2_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f94,f91,f50,f100])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl2_11 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl2_2 | ~spl2_11)),
% 0.21/0.44    inference(resolution,[],[f92,f52])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) ) | ~spl2_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f91])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl2_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f34,f91])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    spl2_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f42,f81])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f40,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl2_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f39,f77])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl2_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f38,f73])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_tops_1(X0,X1),X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ~spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f68])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f10])).
% 0.21/0.45  fof(f10,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f43,f64])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(forward_demodulation,[],[f41,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f32,f37])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f60])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f55])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f50])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f45])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v2_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (18894)------------------------------
% 0.21/0.45  % (18894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (18894)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (18894)Memory used [KB]: 6396
% 0.21/0.45  % (18894)Time elapsed: 0.018 s
% 0.21/0.45  % (18894)------------------------------
% 0.21/0.45  % (18894)------------------------------
% 0.21/0.45  % (18886)Success in time 0.087 s
%------------------------------------------------------------------------------
