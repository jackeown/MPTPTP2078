%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 427 expanded)
%              Number of leaves         :   60 ( 199 expanded)
%              Depth                    :   10
%              Number of atoms          :  686 (1358 expanded)
%              Number of equality atoms :  118 ( 264 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3576,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f91,f93,f97,f101,f105,f109,f122,f126,f138,f147,f151,f155,f159,f163,f192,f199,f203,f215,f222,f231,f239,f243,f255,f267,f344,f425,f467,f515,f587,f604,f750,f805,f809,f1541,f2405,f2608,f2611,f2622,f3202,f3443,f3574])).

fof(f3574,plain,
    ( spl2_4
    | ~ spl2_29
    | ~ spl2_158 ),
    inference(avatar_contradiction_clause,[],[f3573])).

fof(f3573,plain,
    ( $false
    | spl2_4
    | ~ spl2_29
    | ~ spl2_158 ),
    inference(subsumption_resolution,[],[f85,f3550])).

fof(f3550,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_29
    | ~ spl2_158 ),
    inference(superposition,[],[f238,f3442])).

fof(f3442,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_158 ),
    inference(avatar_component_clause,[],[f3440])).

fof(f3440,plain,
    ( spl2_158
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).

fof(f238,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl2_29
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f85,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f3443,plain,
    ( spl2_158
    | ~ spl2_76
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f3203,f3199,f802,f3440])).

fof(f802,plain,
    ( spl2_76
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f3199,plain,
    ( spl2_151
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).

fof(f3203,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_76
    | ~ spl2_151 ),
    inference(superposition,[],[f3201,f804])).

fof(f804,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f802])).

fof(f3201,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_151 ),
    inference(avatar_component_clause,[],[f3199])).

fof(f3202,plain,
    ( spl2_151
    | ~ spl2_59
    | ~ spl2_101 ),
    inference(avatar_split_clause,[],[f1558,f1539,f601,f3199])).

fof(f601,plain,
    ( spl2_59
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f1539,plain,
    ( spl2_101
  <=> ! [X3,X4] :
        ( k2_xboole_0(X4,X3) = X4
        | ~ r1_tarski(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f1558,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_59
    | ~ spl2_101 ),
    inference(unit_resulting_resolution,[],[f603,f1540])).

fof(f1540,plain,
    ( ! [X4,X3] :
        ( k2_xboole_0(X4,X3) = X4
        | ~ r1_tarski(X3,X4) )
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f1539])).

fof(f603,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f601])).

fof(f2622,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | spl2_5
    | ~ spl2_17
    | ~ spl2_30
    | ~ spl2_53
    | ~ spl2_72
    | ~ spl2_76
    | ~ spl2_101 ),
    inference(avatar_contradiction_clause,[],[f2621])).

fof(f2621,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | spl2_5
    | ~ spl2_17
    | ~ spl2_30
    | ~ spl2_53
    | ~ spl2_72
    | ~ spl2_76
    | ~ spl2_101 ),
    inference(subsumption_resolution,[],[f2613,f627])).

fof(f627,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_5
    | ~ spl2_30 ),
    inference(superposition,[],[f89,f242])).

fof(f242,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl2_30
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f89,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f2613,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_53
    | ~ spl2_72
    | ~ spl2_76
    | ~ spl2_101 ),
    inference(forward_demodulation,[],[f749,f2373])).

fof(f2373,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_53
    | ~ spl2_76
    | ~ spl2_101 ),
    inference(subsumption_resolution,[],[f1564,f625])).

fof(f625,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_53 ),
    inference(unit_resulting_resolution,[],[f76,f146,f86,f514])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ v4_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl2_53
  <=> ! [X1,X0] :
        ( ~ v4_pre_topc(X0,X1)
        | r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f86,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f146,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl2_17
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f76,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1564,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_76
    | ~ spl2_101 ),
    inference(superposition,[],[f1540,f804])).

fof(f749,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f747])).

fof(f747,plain,
    ( spl2_72
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f2611,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_53
    | ~ spl2_76
    | ~ spl2_101
    | spl2_136 ),
    inference(avatar_contradiction_clause,[],[f2610])).

fof(f2610,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_53
    | ~ spl2_76
    | ~ spl2_101
    | spl2_136 ),
    inference(subsumption_resolution,[],[f146,f2609])).

fof(f2609,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_53
    | ~ spl2_76
    | ~ spl2_101
    | spl2_136 ),
    inference(forward_demodulation,[],[f2607,f2373])).

fof(f2607,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | spl2_136 ),
    inference(avatar_component_clause,[],[f2605])).

fof(f2605,plain,
    ( spl2_136
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).

fof(f2608,plain,
    ( ~ spl2_136
    | ~ spl2_13
    | spl2_71 ),
    inference(avatar_split_clause,[],[f751,f743,f124,f2605])).

fof(f124,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f743,plain,
    ( spl2_71
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f751,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_13
    | spl2_71 ),
    inference(unit_resulting_resolution,[],[f745,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f745,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_71 ),
    inference(avatar_component_clause,[],[f743])).

fof(f2405,plain,
    ( spl2_59
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f625,f513,f144,f84,f74,f601])).

fof(f1541,plain,
    ( spl2_101
    | ~ spl2_18
    | ~ spl2_40
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f489,f465,f342,f149,f1539])).

fof(f149,plain,
    ( spl2_18
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f342,plain,
    ( spl2_40
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f465,plain,
    ( spl2_50
  <=> ! [X3,X2] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f489,plain,
    ( ! [X4,X3] :
        ( k2_xboole_0(X4,X3) = X4
        | ~ r1_tarski(X3,X4) )
    | ~ spl2_18
    | ~ spl2_40
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f478,f343])).

fof(f343,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f342])).

fof(f478,plain,
    ( ! [X4,X3] :
        ( k2_xboole_0(X4,X3) = k5_xboole_0(X4,k1_xboole_0)
        | ~ r1_tarski(X3,X4) )
    | ~ spl2_18
    | ~ spl2_50 ),
    inference(superposition,[],[f150,f466])).

fof(f466,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f465])).

fof(f150,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f809,plain,
    ( ~ spl2_13
    | ~ spl2_47
    | ~ spl2_59
    | spl2_75 ),
    inference(avatar_contradiction_clause,[],[f808])).

fof(f808,plain,
    ( $false
    | ~ spl2_13
    | ~ spl2_47
    | ~ spl2_59
    | spl2_75 ),
    inference(subsumption_resolution,[],[f605,f806])).

fof(f806,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_13
    | spl2_75 ),
    inference(unit_resulting_resolution,[],[f800,f125])).

fof(f800,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_75 ),
    inference(avatar_component_clause,[],[f798])).

fof(f798,plain,
    ( spl2_75
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f605,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_47
    | ~ spl2_59 ),
    inference(unit_resulting_resolution,[],[f603,f424])).

fof(f424,plain,
    ( ! [X3] :
        ( r1_tarski(X3,u1_struct_0(sK0))
        | ~ r1_tarski(X3,sK1) )
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl2_47
  <=> ! [X3] :
        ( r1_tarski(X3,u1_struct_0(sK0))
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f805,plain,
    ( ~ spl2_3
    | ~ spl2_75
    | spl2_76
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f256,f252,f213,f802,f798,f79])).

fof(f79,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f213,plain,
    ( spl2_26
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f252,plain,
    ( spl2_32
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f256,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(superposition,[],[f254,f214])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f213])).

fof(f254,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f252])).

fof(f750,plain,
    ( ~ spl2_71
    | spl2_72
    | ~ spl2_22
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f270,f264,f190,f747,f743])).

fof(f190,plain,
    ( spl2_22
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f264,plain,
    ( spl2_34
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f270,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_22
    | ~ spl2_34 ),
    inference(superposition,[],[f266,f191])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f190])).

fof(f266,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f264])).

fof(f604,plain,
    ( spl2_59
    | ~ spl2_9
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f590,f259,f107,f601])).

fof(f107,plain,
    ( spl2_9
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f259,plain,
    ( spl2_33
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f590,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_9
    | ~ spl2_33 ),
    inference(superposition,[],[f108,f261])).

fof(f261,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f259])).

fof(f108,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f587,plain,
    ( spl2_33
    | ~ spl2_5
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f244,f241,f88,f259])).

fof(f244,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_30 ),
    inference(superposition,[],[f242,f90])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f515,plain,
    ( spl2_53
    | ~ spl2_13
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f217,f201,f124,f513])).

fof(f201,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,X1)
        | r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | ~ spl2_13
    | ~ spl2_24 ),
    inference(resolution,[],[f202,f125])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f201])).

fof(f467,plain,
    ( spl2_50
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f184,f157,f153,f136,f103,f99,f95,f465])).

fof(f95,plain,
    ( spl2_6
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f99,plain,
    ( spl2_7
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f103,plain,
    ( spl2_8
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f136,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f153,plain,
    ( spl2_19
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f157,plain,
    ( spl2_20
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f184,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f181,f183])).

fof(f183,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f180,f178])).

fof(f178,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f174,f96])).

fof(f96,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f174,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl2_7
    | ~ spl2_19 ),
    inference(superposition,[],[f154,f100])).

fof(f100,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f154,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f180,plain,
    ( ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(superposition,[],[f158,f104])).

fof(f104,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f158,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f181,plain,
    ( ! [X2,X3] :
        ( k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2)
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_16
    | ~ spl2_20 ),
    inference(superposition,[],[f158,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f425,plain,
    ( spl2_47
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f188,f161,f144,f423])).

fof(f161,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f188,plain,
    ( ! [X3] :
        ( r1_tarski(X3,u1_struct_0(sK0))
        | ~ r1_tarski(X3,sK1) )
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(resolution,[],[f162,f146])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f344,plain,
    ( spl2_40
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f182,f157,f99,f95,f342])).

fof(f182,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f179,f100])).

fof(f179,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_20 ),
    inference(superposition,[],[f158,f96])).

fof(f267,plain,
    ( spl2_34
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f232,f229,f79,f74,f264])).

fof(f229,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f232,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f76,f81,f230])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f229])).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f255,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f223,f220,f79,f74,f252])).

fof(f220,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f223,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f76,f81,f221])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f243,plain,
    ( spl2_30
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f193,f190,f79,f241])).

fof(f193,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f81,f191])).

fof(f239,plain,
    ( spl2_29
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f204,f197,f79,f74,f69,f236])).

fof(f69,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f197,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f204,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f198])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f71,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f231,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f51,f229])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f222,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f50,f220])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f215,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f67,f213])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f203,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f52,f201])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f199,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f62,f197])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f192,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f65,f190])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f163,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f66,f161])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f159,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f60,f157])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f155,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f59,f153])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f151,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f58,f149])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f147,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f139,f120,f79,f144])).

fof(f120,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f139,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f81,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f138,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f61,f136])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f126,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f64,f124])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f122,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f63,f120])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f105,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f53,f103])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f101,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f97,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f48,f95])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f93,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f92,f88,f84])).

fof(f92,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f47,f90])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f91,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f46,f88,f84])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f44,f74])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f43,f69])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:47:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (31681)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (31689)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (31683)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (31690)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (31684)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (31685)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (31693)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (31682)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (31692)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (31691)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (31679)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (31680)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (31695)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (31688)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (31694)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (31687)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.53  % (31686)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.53  % (31696)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.59  % (31684)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f3576,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f72,f77,f82,f91,f93,f97,f101,f105,f109,f122,f126,f138,f147,f151,f155,f159,f163,f192,f199,f203,f215,f222,f231,f239,f243,f255,f267,f344,f425,f467,f515,f587,f604,f750,f805,f809,f1541,f2405,f2608,f2611,f2622,f3202,f3443,f3574])).
% 0.22/0.59  fof(f3574,plain,(
% 0.22/0.59    spl2_4 | ~spl2_29 | ~spl2_158),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f3573])).
% 0.22/0.59  fof(f3573,plain,(
% 0.22/0.59    $false | (spl2_4 | ~spl2_29 | ~spl2_158)),
% 0.22/0.59    inference(subsumption_resolution,[],[f85,f3550])).
% 0.22/0.59  fof(f3550,plain,(
% 0.22/0.59    v4_pre_topc(sK1,sK0) | (~spl2_29 | ~spl2_158)),
% 0.22/0.59    inference(superposition,[],[f238,f3442])).
% 0.22/0.59  fof(f3442,plain,(
% 0.22/0.59    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_158),
% 0.22/0.59    inference(avatar_component_clause,[],[f3440])).
% 0.22/0.59  fof(f3440,plain,(
% 0.22/0.59    spl2_158 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).
% 0.22/0.59  fof(f238,plain,(
% 0.22/0.59    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_29),
% 0.22/0.59    inference(avatar_component_clause,[],[f236])).
% 0.22/0.59  fof(f236,plain,(
% 0.22/0.59    spl2_29 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.59  fof(f85,plain,(
% 0.22/0.59    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f84])).
% 0.22/0.59  fof(f84,plain,(
% 0.22/0.59    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.59  fof(f3443,plain,(
% 0.22/0.59    spl2_158 | ~spl2_76 | ~spl2_151),
% 0.22/0.59    inference(avatar_split_clause,[],[f3203,f3199,f802,f3440])).
% 0.22/0.59  fof(f802,plain,(
% 0.22/0.59    spl2_76 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 0.22/0.59  fof(f3199,plain,(
% 0.22/0.59    spl2_151 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).
% 0.22/0.59  fof(f3203,plain,(
% 0.22/0.59    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_76 | ~spl2_151)),
% 0.22/0.59    inference(superposition,[],[f3201,f804])).
% 0.22/0.59  fof(f804,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_76),
% 0.22/0.59    inference(avatar_component_clause,[],[f802])).
% 0.22/0.59  fof(f3201,plain,(
% 0.22/0.59    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_151),
% 0.22/0.59    inference(avatar_component_clause,[],[f3199])).
% 0.22/0.59  fof(f3202,plain,(
% 0.22/0.59    spl2_151 | ~spl2_59 | ~spl2_101),
% 0.22/0.59    inference(avatar_split_clause,[],[f1558,f1539,f601,f3199])).
% 0.22/0.59  fof(f601,plain,(
% 0.22/0.59    spl2_59 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.22/0.59  fof(f1539,plain,(
% 0.22/0.59    spl2_101 <=> ! [X3,X4] : (k2_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,X4))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 0.22/0.59  fof(f1558,plain,(
% 0.22/0.59    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_59 | ~spl2_101)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f603,f1540])).
% 0.22/0.59  fof(f1540,plain,(
% 0.22/0.59    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,X4)) ) | ~spl2_101),
% 0.22/0.59    inference(avatar_component_clause,[],[f1539])).
% 0.22/0.59  fof(f603,plain,(
% 0.22/0.59    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_59),
% 0.22/0.59    inference(avatar_component_clause,[],[f601])).
% 0.22/0.59  fof(f2622,plain,(
% 0.22/0.59    ~spl2_2 | ~spl2_4 | spl2_5 | ~spl2_17 | ~spl2_30 | ~spl2_53 | ~spl2_72 | ~spl2_76 | ~spl2_101),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f2621])).
% 0.22/0.59  fof(f2621,plain,(
% 0.22/0.59    $false | (~spl2_2 | ~spl2_4 | spl2_5 | ~spl2_17 | ~spl2_30 | ~spl2_53 | ~spl2_72 | ~spl2_76 | ~spl2_101)),
% 0.22/0.59    inference(subsumption_resolution,[],[f2613,f627])).
% 0.22/0.59  fof(f627,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (spl2_5 | ~spl2_30)),
% 0.22/0.59    inference(superposition,[],[f89,f242])).
% 0.22/0.59  fof(f242,plain,(
% 0.22/0.59    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_30),
% 0.22/0.59    inference(avatar_component_clause,[],[f241])).
% 0.22/0.59  fof(f241,plain,(
% 0.22/0.59    spl2_30 <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.59  fof(f89,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_5),
% 0.22/0.59    inference(avatar_component_clause,[],[f88])).
% 0.22/0.59  fof(f88,plain,(
% 0.22/0.59    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.59  fof(f2613,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_53 | ~spl2_72 | ~spl2_76 | ~spl2_101)),
% 0.22/0.59    inference(forward_demodulation,[],[f749,f2373])).
% 0.22/0.59  fof(f2373,plain,(
% 0.22/0.59    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_53 | ~spl2_76 | ~spl2_101)),
% 0.22/0.59    inference(subsumption_resolution,[],[f1564,f625])).
% 0.22/0.59  fof(f625,plain,(
% 0.22/0.59    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_53)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f76,f146,f86,f514])).
% 0.22/0.59  fof(f514,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X1,X0),X0) | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) ) | ~spl2_53),
% 0.22/0.59    inference(avatar_component_clause,[],[f513])).
% 0.22/0.59  fof(f513,plain,(
% 0.22/0.59    spl2_53 <=> ! [X1,X0] : (~v4_pre_topc(X0,X1) | r1_tarski(k2_tops_1(X1,X0),X0) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f84])).
% 0.22/0.59  fof(f146,plain,(
% 0.22/0.59    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_17),
% 0.22/0.59    inference(avatar_component_clause,[],[f144])).
% 0.22/0.59  fof(f144,plain,(
% 0.22/0.59    spl2_17 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    l1_pre_topc(sK0) | ~spl2_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f74])).
% 0.22/0.59  fof(f74,plain,(
% 0.22/0.59    spl2_2 <=> l1_pre_topc(sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.59  fof(f1564,plain,(
% 0.22/0.59    sK1 = k2_pre_topc(sK0,sK1) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_76 | ~spl2_101)),
% 0.22/0.59    inference(superposition,[],[f1540,f804])).
% 0.22/0.59  fof(f749,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_72),
% 0.22/0.59    inference(avatar_component_clause,[],[f747])).
% 0.22/0.59  fof(f747,plain,(
% 0.22/0.59    spl2_72 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 0.22/0.59  fof(f2611,plain,(
% 0.22/0.59    ~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_53 | ~spl2_76 | ~spl2_101 | spl2_136),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f2610])).
% 0.22/0.59  fof(f2610,plain,(
% 0.22/0.59    $false | (~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_53 | ~spl2_76 | ~spl2_101 | spl2_136)),
% 0.22/0.59    inference(subsumption_resolution,[],[f146,f2609])).
% 0.22/0.59  fof(f2609,plain,(
% 0.22/0.59    ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_53 | ~spl2_76 | ~spl2_101 | spl2_136)),
% 0.22/0.59    inference(forward_demodulation,[],[f2607,f2373])).
% 0.22/0.59  fof(f2607,plain,(
% 0.22/0.59    ~r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) | spl2_136),
% 0.22/0.59    inference(avatar_component_clause,[],[f2605])).
% 0.22/0.59  fof(f2605,plain,(
% 0.22/0.59    spl2_136 <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).
% 0.22/0.59  fof(f2608,plain,(
% 0.22/0.59    ~spl2_136 | ~spl2_13 | spl2_71),
% 0.22/0.59    inference(avatar_split_clause,[],[f751,f743,f124,f2605])).
% 0.22/0.59  fof(f124,plain,(
% 0.22/0.59    spl2_13 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.59  fof(f743,plain,(
% 0.22/0.59    spl2_71 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.22/0.59  fof(f751,plain,(
% 0.22/0.59    ~r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) | (~spl2_13 | spl2_71)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f745,f125])).
% 0.22/0.59  fof(f125,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.22/0.59    inference(avatar_component_clause,[],[f124])).
% 0.22/0.59  fof(f745,plain,(
% 0.22/0.59    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_71),
% 0.22/0.59    inference(avatar_component_clause,[],[f743])).
% 0.22/0.59  fof(f2405,plain,(
% 0.22/0.59    spl2_59 | ~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_53),
% 0.22/0.59    inference(avatar_split_clause,[],[f625,f513,f144,f84,f74,f601])).
% 0.22/0.59  fof(f1541,plain,(
% 0.22/0.59    spl2_101 | ~spl2_18 | ~spl2_40 | ~spl2_50),
% 0.22/0.59    inference(avatar_split_clause,[],[f489,f465,f342,f149,f1539])).
% 0.22/0.59  fof(f149,plain,(
% 0.22/0.59    spl2_18 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.59  fof(f342,plain,(
% 0.22/0.59    spl2_40 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.22/0.59  fof(f465,plain,(
% 0.22/0.59    spl2_50 <=> ! [X3,X2] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,X3))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.22/0.59  fof(f489,plain,(
% 0.22/0.59    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,X4)) ) | (~spl2_18 | ~spl2_40 | ~spl2_50)),
% 0.22/0.59    inference(forward_demodulation,[],[f478,f343])).
% 0.22/0.59  fof(f343,plain,(
% 0.22/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_40),
% 0.22/0.59    inference(avatar_component_clause,[],[f342])).
% 0.22/0.59  fof(f478,plain,(
% 0.22/0.59    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X4,k1_xboole_0) | ~r1_tarski(X3,X4)) ) | (~spl2_18 | ~spl2_50)),
% 0.22/0.59    inference(superposition,[],[f150,f466])).
% 0.22/0.59  fof(f466,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,X3)) ) | ~spl2_50),
% 0.22/0.59    inference(avatar_component_clause,[],[f465])).
% 0.22/0.59  fof(f150,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_18),
% 0.22/0.59    inference(avatar_component_clause,[],[f149])).
% 0.22/0.59  fof(f809,plain,(
% 0.22/0.59    ~spl2_13 | ~spl2_47 | ~spl2_59 | spl2_75),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f808])).
% 0.22/0.59  fof(f808,plain,(
% 0.22/0.59    $false | (~spl2_13 | ~spl2_47 | ~spl2_59 | spl2_75)),
% 0.22/0.59    inference(subsumption_resolution,[],[f605,f806])).
% 0.22/0.59  fof(f806,plain,(
% 0.22/0.59    ~r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_13 | spl2_75)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f800,f125])).
% 0.22/0.59  fof(f800,plain,(
% 0.22/0.59    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_75),
% 0.22/0.59    inference(avatar_component_clause,[],[f798])).
% 0.22/0.59  fof(f798,plain,(
% 0.22/0.59    spl2_75 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 0.22/0.59  fof(f605,plain,(
% 0.22/0.59    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_47 | ~spl2_59)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f603,f424])).
% 0.22/0.59  fof(f424,plain,(
% 0.22/0.59    ( ! [X3] : (r1_tarski(X3,u1_struct_0(sK0)) | ~r1_tarski(X3,sK1)) ) | ~spl2_47),
% 0.22/0.59    inference(avatar_component_clause,[],[f423])).
% 0.22/0.59  fof(f423,plain,(
% 0.22/0.59    spl2_47 <=> ! [X3] : (r1_tarski(X3,u1_struct_0(sK0)) | ~r1_tarski(X3,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.22/0.59  fof(f805,plain,(
% 0.22/0.59    ~spl2_3 | ~spl2_75 | spl2_76 | ~spl2_26 | ~spl2_32),
% 0.22/0.59    inference(avatar_split_clause,[],[f256,f252,f213,f802,f798,f79])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.59  fof(f213,plain,(
% 0.22/0.59    spl2_26 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.59  fof(f252,plain,(
% 0.22/0.59    spl2_32 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.59  fof(f256,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_26 | ~spl2_32)),
% 0.22/0.59    inference(superposition,[],[f254,f214])).
% 0.22/0.59  fof(f214,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_26),
% 0.22/0.59    inference(avatar_component_clause,[],[f213])).
% 0.22/0.59  fof(f254,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_32),
% 0.22/0.59    inference(avatar_component_clause,[],[f252])).
% 0.22/0.59  fof(f750,plain,(
% 0.22/0.59    ~spl2_71 | spl2_72 | ~spl2_22 | ~spl2_34),
% 0.22/0.59    inference(avatar_split_clause,[],[f270,f264,f190,f747,f743])).
% 0.22/0.59  fof(f190,plain,(
% 0.22/0.59    spl2_22 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.59  fof(f264,plain,(
% 0.22/0.59    spl2_34 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.22/0.59  fof(f270,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_22 | ~spl2_34)),
% 0.22/0.59    inference(superposition,[],[f266,f191])).
% 0.22/0.59  fof(f191,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_22),
% 0.22/0.59    inference(avatar_component_clause,[],[f190])).
% 0.22/0.59  fof(f266,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_34),
% 0.22/0.59    inference(avatar_component_clause,[],[f264])).
% 0.22/0.59  fof(f604,plain,(
% 0.22/0.59    spl2_59 | ~spl2_9 | ~spl2_33),
% 0.22/0.59    inference(avatar_split_clause,[],[f590,f259,f107,f601])).
% 0.22/0.59  fof(f107,plain,(
% 0.22/0.59    spl2_9 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.59  fof(f259,plain,(
% 0.22/0.59    spl2_33 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.22/0.59  fof(f590,plain,(
% 0.22/0.59    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_9 | ~spl2_33)),
% 0.22/0.59    inference(superposition,[],[f108,f261])).
% 0.22/0.59  fof(f261,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_33),
% 0.22/0.59    inference(avatar_component_clause,[],[f259])).
% 0.22/0.59  fof(f108,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_9),
% 0.22/0.59    inference(avatar_component_clause,[],[f107])).
% 0.22/0.59  fof(f587,plain,(
% 0.22/0.59    spl2_33 | ~spl2_5 | ~spl2_30),
% 0.22/0.59    inference(avatar_split_clause,[],[f244,f241,f88,f259])).
% 0.22/0.59  fof(f244,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_30)),
% 0.22/0.59    inference(superposition,[],[f242,f90])).
% 0.22/0.59  fof(f90,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.22/0.59    inference(avatar_component_clause,[],[f88])).
% 0.22/0.59  fof(f515,plain,(
% 0.22/0.59    spl2_53 | ~spl2_13 | ~spl2_24),
% 0.22/0.59    inference(avatar_split_clause,[],[f217,f201,f124,f513])).
% 0.22/0.59  fof(f201,plain,(
% 0.22/0.59    spl2_24 <=> ! [X1,X0] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.59  fof(f217,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v4_pre_topc(X0,X1) | r1_tarski(k2_tops_1(X1,X0),X0) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) ) | (~spl2_13 | ~spl2_24)),
% 0.22/0.59    inference(resolution,[],[f202,f125])).
% 0.22/0.59  fof(f202,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_24),
% 0.22/0.59    inference(avatar_component_clause,[],[f201])).
% 0.22/0.59  fof(f467,plain,(
% 0.22/0.59    spl2_50 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_16 | ~spl2_19 | ~spl2_20),
% 0.22/0.59    inference(avatar_split_clause,[],[f184,f157,f153,f136,f103,f99,f95,f465])).
% 0.22/0.59  fof(f95,plain,(
% 0.22/0.59    spl2_6 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.59  fof(f99,plain,(
% 0.22/0.59    spl2_7 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.59  fof(f103,plain,(
% 0.22/0.59    spl2_8 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.59  fof(f136,plain,(
% 0.22/0.59    spl2_16 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.59  fof(f153,plain,(
% 0.22/0.59    spl2_19 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.59  fof(f157,plain,(
% 0.22/0.59    spl2_20 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.59  fof(f184,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,X3)) ) | (~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_16 | ~spl2_19 | ~spl2_20)),
% 0.22/0.59    inference(forward_demodulation,[],[f181,f183])).
% 0.22/0.59  fof(f183,plain,(
% 0.22/0.59    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) ) | (~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_19 | ~spl2_20)),
% 0.22/0.59    inference(forward_demodulation,[],[f180,f178])).
% 0.22/0.59  fof(f178,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_6 | ~spl2_7 | ~spl2_19)),
% 0.22/0.59    inference(forward_demodulation,[],[f174,f96])).
% 0.22/0.59  fof(f96,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_6),
% 0.22/0.59    inference(avatar_component_clause,[],[f95])).
% 0.22/0.59  fof(f174,plain,(
% 0.22/0.59    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl2_7 | ~spl2_19)),
% 0.22/0.59    inference(superposition,[],[f154,f100])).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_7),
% 0.22/0.59    inference(avatar_component_clause,[],[f99])).
% 0.22/0.59  fof(f154,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_19),
% 0.22/0.59    inference(avatar_component_clause,[],[f153])).
% 0.22/0.59  fof(f180,plain,(
% 0.22/0.59    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) ) | (~spl2_8 | ~spl2_20)),
% 0.22/0.59    inference(superposition,[],[f158,f104])).
% 0.22/0.59  fof(f104,plain,(
% 0.22/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl2_8),
% 0.22/0.59    inference(avatar_component_clause,[],[f103])).
% 0.22/0.59  fof(f158,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_20),
% 0.22/0.59    inference(avatar_component_clause,[],[f157])).
% 0.22/0.59  fof(f181,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) ) | (~spl2_16 | ~spl2_20)),
% 0.22/0.59    inference(superposition,[],[f158,f137])).
% 0.22/0.59  fof(f137,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_16),
% 0.22/0.59    inference(avatar_component_clause,[],[f136])).
% 0.22/0.59  fof(f425,plain,(
% 0.22/0.59    spl2_47 | ~spl2_17 | ~spl2_21),
% 0.22/0.59    inference(avatar_split_clause,[],[f188,f161,f144,f423])).
% 0.22/0.59  fof(f161,plain,(
% 0.22/0.59    spl2_21 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.59  fof(f188,plain,(
% 0.22/0.59    ( ! [X3] : (r1_tarski(X3,u1_struct_0(sK0)) | ~r1_tarski(X3,sK1)) ) | (~spl2_17 | ~spl2_21)),
% 0.22/0.59    inference(resolution,[],[f162,f146])).
% 0.22/0.59  fof(f162,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_21),
% 0.22/0.59    inference(avatar_component_clause,[],[f161])).
% 0.22/0.59  fof(f344,plain,(
% 0.22/0.59    spl2_40 | ~spl2_6 | ~spl2_7 | ~spl2_20),
% 0.22/0.59    inference(avatar_split_clause,[],[f182,f157,f99,f95,f342])).
% 0.22/0.59  fof(f182,plain,(
% 0.22/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_6 | ~spl2_7 | ~spl2_20)),
% 0.22/0.59    inference(forward_demodulation,[],[f179,f100])).
% 0.22/0.59  fof(f179,plain,(
% 0.22/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) ) | (~spl2_6 | ~spl2_20)),
% 0.22/0.59    inference(superposition,[],[f158,f96])).
% 0.22/0.59  fof(f267,plain,(
% 0.22/0.59    spl2_34 | ~spl2_2 | ~spl2_3 | ~spl2_28),
% 0.22/0.59    inference(avatar_split_clause,[],[f232,f229,f79,f74,f264])).
% 0.22/0.59  fof(f229,plain,(
% 0.22/0.59    spl2_28 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.59  fof(f232,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_28)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f76,f81,f230])).
% 0.22/0.59  fof(f230,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_28),
% 0.22/0.59    inference(avatar_component_clause,[],[f229])).
% 0.22/0.59  fof(f81,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.59    inference(avatar_component_clause,[],[f79])).
% 0.22/0.59  fof(f255,plain,(
% 0.22/0.59    spl2_32 | ~spl2_2 | ~spl2_3 | ~spl2_27),
% 0.22/0.59    inference(avatar_split_clause,[],[f223,f220,f79,f74,f252])).
% 0.22/0.59  fof(f220,plain,(
% 0.22/0.59    spl2_27 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.59  fof(f223,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_27)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f76,f81,f221])).
% 0.22/0.59  fof(f221,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_27),
% 0.22/0.59    inference(avatar_component_clause,[],[f220])).
% 0.22/0.59  fof(f243,plain,(
% 0.22/0.59    spl2_30 | ~spl2_3 | ~spl2_22),
% 0.22/0.59    inference(avatar_split_clause,[],[f193,f190,f79,f241])).
% 0.22/0.59  fof(f193,plain,(
% 0.22/0.59    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl2_3 | ~spl2_22)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f81,f191])).
% 0.22/0.59  fof(f239,plain,(
% 0.22/0.59    spl2_29 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_23),
% 0.22/0.59    inference(avatar_split_clause,[],[f204,f197,f79,f74,f69,f236])).
% 0.22/0.60  fof(f69,plain,(
% 0.22/0.60    spl2_1 <=> v2_pre_topc(sK0)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.60  fof(f197,plain,(
% 0.22/0.60    spl2_23 <=> ! [X1,X0] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.60  fof(f204,plain,(
% 0.22/0.60    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_23)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f71,f76,f81,f198])).
% 0.22/0.60  fof(f198,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_23),
% 0.22/0.60    inference(avatar_component_clause,[],[f197])).
% 0.22/0.60  fof(f71,plain,(
% 0.22/0.60    v2_pre_topc(sK0) | ~spl2_1),
% 0.22/0.60    inference(avatar_component_clause,[],[f69])).
% 0.22/0.60  fof(f231,plain,(
% 0.22/0.60    spl2_28),
% 0.22/0.60    inference(avatar_split_clause,[],[f51,f229])).
% 0.22/0.60  fof(f51,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,axiom,(
% 0.22/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.60  fof(f222,plain,(
% 0.22/0.60    spl2_27),
% 0.22/0.60    inference(avatar_split_clause,[],[f50,f220])).
% 0.22/0.60  fof(f50,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f18])).
% 0.22/0.60  fof(f18,axiom,(
% 0.22/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.60  fof(f215,plain,(
% 0.22/0.60    spl2_26),
% 0.22/0.60    inference(avatar_split_clause,[],[f67,f213])).
% 0.22/0.60  fof(f67,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f36])).
% 0.22/0.60  fof(f36,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.60    inference(flattening,[],[f35])).
% 0.22/0.60  fof(f35,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.60    inference(ennf_transformation,[],[f12])).
% 0.22/0.60  fof(f12,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.60  fof(f203,plain,(
% 0.22/0.60    spl2_24),
% 0.22/0.60    inference(avatar_split_clause,[],[f52,f201])).
% 0.22/0.60  fof(f52,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f28])).
% 0.22/0.60  fof(f28,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.60    inference(flattening,[],[f27])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f19])).
% 0.22/0.60  fof(f19,axiom,(
% 0.22/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 0.22/0.60  fof(f199,plain,(
% 0.22/0.60    spl2_23),
% 0.22/0.60    inference(avatar_split_clause,[],[f62,f197])).
% 0.22/0.60  fof(f62,plain,(
% 0.22/0.60    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f31])).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.60    inference(flattening,[],[f30])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f16])).
% 0.22/0.60  fof(f16,axiom,(
% 0.22/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.60  fof(f192,plain,(
% 0.22/0.60    spl2_22),
% 0.22/0.60    inference(avatar_split_clause,[],[f65,f190])).
% 0.22/0.60  fof(f65,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f32])).
% 0.22/0.60  fof(f32,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f13])).
% 0.22/0.60  fof(f13,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.60  fof(f163,plain,(
% 0.22/0.60    spl2_21),
% 0.22/0.60    inference(avatar_split_clause,[],[f66,f161])).
% 0.22/0.60  fof(f66,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f34])).
% 0.22/0.60  fof(f34,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.60    inference(flattening,[],[f33])).
% 0.22/0.60  fof(f33,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.60    inference(ennf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.60  fof(f159,plain,(
% 0.22/0.60    spl2_20),
% 0.22/0.60    inference(avatar_split_clause,[],[f60,f157])).
% 0.22/0.60  fof(f60,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.60  fof(f155,plain,(
% 0.22/0.60    spl2_19),
% 0.22/0.60    inference(avatar_split_clause,[],[f59,f153])).
% 0.22/0.60  fof(f59,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f8])).
% 0.22/0.60  fof(f8,axiom,(
% 0.22/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.60  fof(f151,plain,(
% 0.22/0.60    spl2_18),
% 0.22/0.60    inference(avatar_split_clause,[],[f58,f149])).
% 0.22/0.60  fof(f58,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f9])).
% 0.22/0.60  fof(f9,axiom,(
% 0.22/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.60  fof(f147,plain,(
% 0.22/0.60    spl2_17 | ~spl2_3 | ~spl2_12),
% 0.22/0.60    inference(avatar_split_clause,[],[f139,f120,f79,f144])).
% 0.22/0.60  fof(f120,plain,(
% 0.22/0.60    spl2_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.60  fof(f139,plain,(
% 0.22/0.60    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_3 | ~spl2_12)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f81,f121])).
% 0.22/0.60  fof(f121,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_12),
% 0.22/0.60    inference(avatar_component_clause,[],[f120])).
% 0.22/0.60  fof(f138,plain,(
% 0.22/0.60    spl2_16),
% 0.22/0.60    inference(avatar_split_clause,[],[f61,f136])).
% 0.22/0.60  fof(f61,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f29])).
% 0.22/0.60  fof(f29,plain,(
% 0.22/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.60    inference(ennf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.60  fof(f126,plain,(
% 0.22/0.60    spl2_13),
% 0.22/0.60    inference(avatar_split_clause,[],[f64,f124])).
% 0.22/0.60  fof(f64,plain,(
% 0.22/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f42])).
% 0.22/0.60  fof(f42,plain,(
% 0.22/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.60    inference(nnf_transformation,[],[f15])).
% 0.22/0.60  fof(f15,axiom,(
% 0.22/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.60  fof(f122,plain,(
% 0.22/0.60    spl2_12),
% 0.22/0.60    inference(avatar_split_clause,[],[f63,f120])).
% 0.22/0.60  fof(f63,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f42])).
% 0.22/0.60  fof(f109,plain,(
% 0.22/0.60    spl2_9),
% 0.22/0.60    inference(avatar_split_clause,[],[f54,f107])).
% 0.22/0.60  fof(f54,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f6])).
% 0.22/0.60  fof(f6,axiom,(
% 0.22/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.60  fof(f105,plain,(
% 0.22/0.60    spl2_8),
% 0.22/0.60    inference(avatar_split_clause,[],[f53,f103])).
% 0.22/0.60  fof(f53,plain,(
% 0.22/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.60    inference(rectify,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.60  fof(f101,plain,(
% 0.22/0.60    spl2_7),
% 0.22/0.60    inference(avatar_split_clause,[],[f49,f99])).
% 0.22/0.60  fof(f49,plain,(
% 0.22/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f7])).
% 0.22/0.60  fof(f7,axiom,(
% 0.22/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.60  fof(f97,plain,(
% 0.22/0.60    spl2_6),
% 0.22/0.60    inference(avatar_split_clause,[],[f48,f95])).
% 0.22/0.60  fof(f48,plain,(
% 0.22/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.60  fof(f93,plain,(
% 0.22/0.60    ~spl2_4 | ~spl2_5),
% 0.22/0.60    inference(avatar_split_clause,[],[f92,f88,f84])).
% 0.22/0.60  fof(f92,plain,(
% 0.22/0.60    ~v4_pre_topc(sK1,sK0) | ~spl2_5),
% 0.22/0.60    inference(subsumption_resolution,[],[f47,f90])).
% 0.22/0.60  fof(f47,plain,(
% 0.22/0.60    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f41])).
% 0.22/0.60  fof(f41,plain,(
% 0.22/0.60    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.22/0.60  fof(f39,plain,(
% 0.22/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f40,plain,(
% 0.22/0.60    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f38,plain,(
% 0.22/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.60    inference(flattening,[],[f37])).
% 0.22/0.60  fof(f37,plain,(
% 0.22/0.60    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.60    inference(nnf_transformation,[],[f24])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.60    inference(flattening,[],[f23])).
% 0.22/0.60  fof(f23,plain,(
% 0.22/0.60    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f21])).
% 0.22/0.60  fof(f21,negated_conjecture,(
% 0.22/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.60    inference(negated_conjecture,[],[f20])).
% 0.22/0.60  fof(f20,conjecture,(
% 0.22/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.60  fof(f91,plain,(
% 0.22/0.60    spl2_4 | spl2_5),
% 0.22/0.60    inference(avatar_split_clause,[],[f46,f88,f84])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f41])).
% 0.22/0.60  fof(f82,plain,(
% 0.22/0.60    spl2_3),
% 0.22/0.60    inference(avatar_split_clause,[],[f45,f79])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.60    inference(cnf_transformation,[],[f41])).
% 0.22/0.60  fof(f77,plain,(
% 0.22/0.60    spl2_2),
% 0.22/0.60    inference(avatar_split_clause,[],[f44,f74])).
% 0.22/0.60  fof(f44,plain,(
% 0.22/0.60    l1_pre_topc(sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f41])).
% 0.22/0.60  fof(f72,plain,(
% 0.22/0.60    spl2_1),
% 0.22/0.60    inference(avatar_split_clause,[],[f43,f69])).
% 0.22/0.60  fof(f43,plain,(
% 0.22/0.60    v2_pre_topc(sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f41])).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (31684)------------------------------
% 0.22/0.60  % (31684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (31684)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (31684)Memory used [KB]: 8827
% 0.22/0.60  % (31684)Time elapsed: 0.169 s
% 0.22/0.60  % (31684)------------------------------
% 0.22/0.60  % (31684)------------------------------
% 0.22/0.60  % (31678)Success in time 0.235 s
%------------------------------------------------------------------------------
