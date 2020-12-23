%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:53 EST 2020

% Result     : Theorem 37.20s
% Output     : Refutation 37.20s
% Verified   : 
% Statistics : Number of formulae       :  519 (1163 expanded)
%              Number of leaves         :  125 ( 568 expanded)
%              Depth                    :   13
%              Number of atoms          : 1595 (3279 expanded)
%              Number of equality atoms :  270 ( 701 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f116,f125,f129,f133,f137,f141,f145,f151,f164,f174,f188,f201,f206,f211,f215,f229,f243,f253,f285,f292,f331,f388,f392,f407,f411,f441,f469,f482,f486,f499,f602,f770,f904,f1165,f1174,f1391,f1525,f1560,f1597,f2118,f2124,f2131,f2152,f2294,f2525,f2568,f2756,f2783,f2790,f2841,f3044,f3170,f3342,f3346,f3350,f3484,f3816,f3998,f4045,f4900,f4910,f4952,f5376,f5632,f5636,f5738,f10518,f10710,f10852,f10875,f10922,f10963,f10967,f10971,f11270,f11290,f11643,f11988,f15618,f16574,f17183,f17464,f17942,f17949,f18492,f18709,f19247,f19307,f19518,f19540,f19583,f23327,f23375,f73289,f73294,f77178,f81454])).

fof(f81454,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | spl2_34
    | ~ spl2_44
    | ~ spl2_286 ),
    inference(avatar_contradiction_clause,[],[f81453])).

fof(f81453,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | spl2_34
    | ~ spl2_44
    | ~ spl2_286 ),
    inference(subsumption_resolution,[],[f81452,f110])).

fof(f110,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f81452,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_4
    | spl2_34
    | ~ spl2_44
    | ~ spl2_286 ),
    inference(subsumption_resolution,[],[f81451,f115])).

fof(f115,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f81451,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_4
    | spl2_34
    | ~ spl2_44
    | ~ spl2_286 ),
    inference(subsumption_resolution,[],[f81450,f124])).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f81450,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_34
    | ~ spl2_44
    | ~ spl2_286 ),
    inference(subsumption_resolution,[],[f81442,f325])).

fof(f325,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_34 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl2_34
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f81442,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_44
    | ~ spl2_286 ),
    inference(superposition,[],[f406,f4909])).

fof(f4909,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_286 ),
    inference(avatar_component_clause,[],[f4907])).

fof(f4907,plain,
    ( spl2_286
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_286])])).

fof(f406,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl2_44
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f77178,plain,
    ( ~ spl2_181
    | spl2_286
    | ~ spl2_573
    | ~ spl2_740
    | ~ spl2_1596
    | ~ spl2_1597 ),
    inference(avatar_contradiction_clause,[],[f77177])).

fof(f77177,plain,
    ( $false
    | ~ spl2_181
    | spl2_286
    | ~ spl2_573
    | ~ spl2_740
    | ~ spl2_1596
    | ~ spl2_1597 ),
    inference(subsumption_resolution,[],[f77176,f4908])).

fof(f4908,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_286 ),
    inference(avatar_component_clause,[],[f4907])).

fof(f77176,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_181
    | ~ spl2_573
    | ~ spl2_740
    | ~ spl2_1596
    | ~ spl2_1597 ),
    inference(forward_demodulation,[],[f75563,f19539])).

fof(f19539,plain,
    ( sK1 = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,sK1)
    | ~ spl2_573 ),
    inference(avatar_component_clause,[],[f19537])).

fof(f19537,plain,
    ( spl2_573
  <=> sK1 = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_573])])).

fof(f75563,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,sK1)
    | ~ spl2_181
    | ~ spl2_740
    | ~ spl2_1596
    | ~ spl2_1597 ),
    inference(backward_demodulation,[],[f73288,f74373])).

fof(f74373,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_181
    | ~ spl2_740
    | ~ spl2_1597 ),
    inference(subsumption_resolution,[],[f74343,f23374])).

fof(f23374,plain,
    ( r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl2_740 ),
    inference(avatar_component_clause,[],[f23372])).

fof(f23372,plain,
    ( spl2_740
  <=> r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_740])])).

fof(f74343,plain,
    ( ~ r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | k1_xboole_0 = k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_181
    | ~ spl2_1597 ),
    inference(superposition,[],[f2840,f73293])).

fof(f73293,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_1597 ),
    inference(avatar_component_clause,[],[f73291])).

fof(f73291,plain,
    ( spl2_1597
  <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1597])])).

fof(f2840,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k7_subset_1(X1,X1,X0))
        | k1_xboole_0 = X0 )
    | ~ spl2_181 ),
    inference(avatar_component_clause,[],[f2839])).

fof(f2839,plain,
    ( spl2_181
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k7_subset_1(X1,X1,X0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).

fof(f73288,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl2_1596 ),
    inference(avatar_component_clause,[],[f73286])).

fof(f73286,plain,
    ( spl2_1596
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1596])])).

fof(f73294,plain,
    ( spl2_1597
    | ~ spl2_22
    | ~ spl2_368
    | ~ spl2_413
    | ~ spl2_562
    | ~ spl2_572
    | ~ spl2_576 ),
    inference(avatar_split_clause,[],[f19626,f19580,f19515,f19304,f11986,f10516,f227,f73291])).

fof(f227,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f10516,plain,
    ( spl2_368
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_368])])).

fof(f11986,plain,
    ( spl2_413
  <=> ! [X1,X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_413])])).

fof(f19304,plain,
    ( spl2_562
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_562])])).

fof(f19515,plain,
    ( spl2_572
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_572])])).

fof(f19580,plain,
    ( spl2_576
  <=> r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_576])])).

fof(f19626,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_22
    | ~ spl2_368
    | ~ spl2_413
    | ~ spl2_562
    | ~ spl2_572
    | ~ spl2_576 ),
    inference(forward_demodulation,[],[f19618,f19534])).

fof(f19534,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_22
    | ~ spl2_368
    | ~ spl2_413
    | ~ spl2_562
    | ~ spl2_572 ),
    inference(backward_demodulation,[],[f19311,f19531])).

fof(f19531,plain,
    ( k5_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_368
    | ~ spl2_413
    | ~ spl2_562
    | ~ spl2_572 ),
    inference(backward_demodulation,[],[f19315,f19527])).

fof(f19527,plain,
    ( k5_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_413
    | ~ spl2_572 ),
    inference(superposition,[],[f11987,f19517])).

fof(f19517,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_572 ),
    inference(avatar_component_clause,[],[f19515])).

fof(f11987,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)
    | ~ spl2_413 ),
    inference(avatar_component_clause,[],[f11986])).

fof(f19315,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_368
    | ~ spl2_562 ),
    inference(resolution,[],[f19306,f10517])).

fof(f10517,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )
    | ~ spl2_368 ),
    inference(avatar_component_clause,[],[f10516])).

fof(f19306,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_562 ),
    inference(avatar_component_clause,[],[f19304])).

fof(f19311,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_22
    | ~ spl2_562 ),
    inference(resolution,[],[f19306,f228])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f19618,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_368
    | ~ spl2_576 ),
    inference(resolution,[],[f19582,f10517])).

fof(f19582,plain,
    ( r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_576 ),
    inference(avatar_component_clause,[],[f19580])).

fof(f73289,plain,
    ( spl2_1596
    | ~ spl2_22
    | ~ spl2_45
    | ~ spl2_368
    | ~ spl2_413
    | ~ spl2_562
    | ~ spl2_572
    | ~ spl2_576 ),
    inference(avatar_split_clause,[],[f19624,f19580,f19515,f19304,f11986,f10516,f409,f227,f73286])).

fof(f409,plain,
    ( spl2_45
  <=> ! [X1,X0] :
        ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f19624,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl2_22
    | ~ spl2_45
    | ~ spl2_368
    | ~ spl2_413
    | ~ spl2_562
    | ~ spl2_572
    | ~ spl2_576 ),
    inference(forward_demodulation,[],[f19615,f19534])).

fof(f19615,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_45
    | ~ spl2_576 ),
    inference(resolution,[],[f19582,f410])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f409])).

fof(f23375,plain,
    ( spl2_740
    | ~ spl2_463
    | ~ spl2_738 ),
    inference(avatar_split_clause,[],[f23357,f23325,f15615,f23372])).

fof(f15615,plain,
    ( spl2_463
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_463])])).

fof(f23325,plain,
    ( spl2_738
  <=> ! [X11] :
        ( r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),X11)
        | ~ r1_tarski(k2_tops_1(sK0,sK1),X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_738])])).

fof(f23357,plain,
    ( r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl2_463
    | ~ spl2_738 ),
    inference(resolution,[],[f23326,f15617])).

fof(f15617,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_463 ),
    inference(avatar_component_clause,[],[f15615])).

fof(f23326,plain,
    ( ! [X11] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),X11)
        | r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),X11) )
    | ~ spl2_738 ),
    inference(avatar_component_clause,[],[f23325])).

fof(f23327,plain,
    ( spl2_738
    | ~ spl2_382
    | ~ spl2_560 ),
    inference(avatar_split_clause,[],[f19283,f19244,f10961,f23325])).

fof(f10961,plain,
    ( spl2_382
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X2,X0)),X2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_382])])).

fof(f19244,plain,
    ( spl2_560
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_560])])).

fof(f19283,plain,
    ( ! [X11] :
        ( r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),X11)
        | ~ r1_tarski(k2_tops_1(sK0,sK1),X11) )
    | ~ spl2_382
    | ~ spl2_560 ),
    inference(superposition,[],[f10962,f19246])).

fof(f19246,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_560 ),
    inference(avatar_component_clause,[],[f19244])).

fof(f10962,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X2,X0)),X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_382 ),
    inference(avatar_component_clause,[],[f10961])).

fof(f19583,plain,
    ( spl2_576
    | ~ spl2_384
    | ~ spl2_560 ),
    inference(avatar_split_clause,[],[f19284,f19244,f10969,f19580])).

fof(f10969,plain,
    ( spl2_384
  <=> ! [X1,X0] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_384])])).

fof(f19284,plain,
    ( r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_384
    | ~ spl2_560 ),
    inference(superposition,[],[f10970,f19246])).

fof(f10970,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))
    | ~ spl2_384 ),
    inference(avatar_component_clause,[],[f10969])).

fof(f19540,plain,
    ( spl2_573
    | ~ spl2_376
    | ~ spl2_560 ),
    inference(avatar_split_clause,[],[f19281,f19244,f10920,f19537])).

fof(f10920,plain,
    ( spl2_376
  <=> ! [X1,X2] : k4_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_376])])).

fof(f19281,plain,
    ( sK1 = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,sK1)
    | ~ spl2_376
    | ~ spl2_560 ),
    inference(superposition,[],[f10921,f19246])).

fof(f10921,plain,
    ( ! [X2,X1] : k4_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0,X1) = X1
    | ~ spl2_376 ),
    inference(avatar_component_clause,[],[f10920])).

fof(f19518,plain,
    ( spl2_572
    | ~ spl2_325
    | ~ spl2_560 ),
    inference(avatar_split_clause,[],[f19279,f19244,f5630,f19515])).

fof(f5630,plain,
    ( spl2_325
  <=> ! [X3,X2] : k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3)))) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_325])])).

fof(f19279,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_325
    | ~ spl2_560 ),
    inference(superposition,[],[f5631,f19246])).

fof(f5631,plain,
    ( ! [X2,X3] : k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3)))) = X2
    | ~ spl2_325 ),
    inference(avatar_component_clause,[],[f5630])).

fof(f19307,plain,
    ( spl2_562
    | ~ spl2_131
    | ~ spl2_560 ),
    inference(avatar_split_clause,[],[f19261,f19244,f1558,f19304])).

fof(f1558,plain,
    ( spl2_131
  <=> ! [X1,X0] : r1_tarski(X1,k3_tarski(k2_tarski(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).

fof(f19261,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_131
    | ~ spl2_560 ),
    inference(superposition,[],[f1559,f19246])).

fof(f1559,plain,
    ( ! [X0,X1] : r1_tarski(X1,k3_tarski(k2_tarski(X1,X0)))
    | ~ spl2_131 ),
    inference(avatar_component_clause,[],[f1558])).

fof(f19247,plain,
    ( spl2_560
    | ~ spl2_4
    | ~ spl2_103
    | ~ spl2_485
    | ~ spl2_509 ),
    inference(avatar_split_clause,[],[f18494,f17462,f16572,f1171,f122,f19244])).

fof(f1171,plain,
    ( spl2_103
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f16572,plain,
    ( spl2_485
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_tarski(k2_tarski(sK1,X2)) = k4_subset_1(u1_struct_0(sK0),sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_485])])).

fof(f17462,plain,
    ( spl2_509
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_509])])).

fof(f18494,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_103
    | ~ spl2_485
    | ~ spl2_509 ),
    inference(backward_demodulation,[],[f16878,f18037])).

fof(f18037,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_509 ),
    inference(resolution,[],[f17463,f124])).

fof(f17463,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_509 ),
    inference(avatar_component_clause,[],[f17462])).

fof(f16878,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_103
    | ~ spl2_485 ),
    inference(resolution,[],[f16573,f1173])).

fof(f1173,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_103 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f16573,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_tarski(k2_tarski(sK1,X2)) = k4_subset_1(u1_struct_0(sK0),sK1,X2) )
    | ~ spl2_485 ),
    inference(avatar_component_clause,[],[f16572])).

fof(f18709,plain,
    ( ~ spl2_7
    | ~ spl2_34
    | ~ spl2_175
    | ~ spl2_289
    | ~ spl2_326
    | ~ spl2_390
    | ~ spl2_402
    | ~ spl2_524
    | ~ spl2_533 ),
    inference(avatar_contradiction_clause,[],[f18708])).

fof(f18708,plain,
    ( $false
    | ~ spl2_7
    | ~ spl2_34
    | ~ spl2_175
    | ~ spl2_289
    | ~ spl2_326
    | ~ spl2_390
    | ~ spl2_402
    | ~ spl2_524
    | ~ spl2_533 ),
    inference(subsumption_resolution,[],[f18707,f18658])).

fof(f18658,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_34
    | ~ spl2_175
    | ~ spl2_289
    | ~ spl2_390
    | ~ spl2_402
    | ~ spl2_524 ),
    inference(subsumption_resolution,[],[f18493,f326])).

fof(f326,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f324])).

fof(f18493,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_175
    | ~ spl2_289
    | ~ spl2_390
    | ~ spl2_402
    | ~ spl2_524 ),
    inference(forward_demodulation,[],[f2791,f17976])).

fof(f17976,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_289
    | ~ spl2_390
    | ~ spl2_402
    | ~ spl2_524 ),
    inference(backward_demodulation,[],[f17975,f17969])).

fof(f17969,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_402
    | ~ spl2_524 ),
    inference(superposition,[],[f11642,f17948])).

fof(f17948,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_524 ),
    inference(avatar_component_clause,[],[f17946])).

fof(f17946,plain,
    ( spl2_524
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_524])])).

fof(f11642,plain,
    ( ! [X50,X49] : k3_subset_1(X49,k7_subset_1(X49,X49,X50)) = k1_setfam_1(k2_tarski(X49,X50))
    | ~ spl2_402 ),
    inference(avatar_component_clause,[],[f11641])).

fof(f11641,plain,
    ( spl2_402
  <=> ! [X49,X50] : k3_subset_1(X49,k7_subset_1(X49,X49,X50)) = k1_setfam_1(k2_tarski(X49,X50)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_402])])).

fof(f17975,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_289
    | ~ spl2_390
    | ~ spl2_524 ),
    inference(forward_demodulation,[],[f17967,f11269])).

fof(f11269,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) = k7_subset_1(X3,X3,X4)
    | ~ spl2_390 ),
    inference(avatar_component_clause,[],[f11268])).

fof(f11268,plain,
    ( spl2_390
  <=> ! [X3,X4] : k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) = k7_subset_1(X3,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_390])])).

fof(f17967,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))
    | ~ spl2_289
    | ~ spl2_524 ),
    inference(superposition,[],[f4951,f17948])).

fof(f4951,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))))
    | ~ spl2_289 ),
    inference(avatar_component_clause,[],[f4950])).

fof(f4950,plain,
    ( spl2_289
  <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_289])])).

fof(f2791,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_175 ),
    inference(forward_demodulation,[],[f63,f2782])).

fof(f2782,plain,
    ( ! [X21] : k7_subset_1(u1_struct_0(sK0),sK1,X21) = k7_subset_1(sK1,sK1,X21)
    | ~ spl2_175 ),
    inference(avatar_component_clause,[],[f2781])).

fof(f2781,plain,
    ( spl2_175
  <=> ! [X21] : k7_subset_1(u1_struct_0(sK0),sK1,X21) = k7_subset_1(sK1,sK1,X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_175])])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f55,plain,
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

fof(f56,plain,
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

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f18707,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_326
    | ~ spl2_402
    | ~ spl2_524
    | ~ spl2_533 ),
    inference(backward_demodulation,[],[f17969,f18706])).

fof(f18706,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_7
    | ~ spl2_326
    | ~ spl2_533 ),
    inference(forward_demodulation,[],[f18689,f136])).

fof(f136,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f18689,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_326
    | ~ spl2_533 ),
    inference(superposition,[],[f5635,f18491])).

fof(f18491,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_533 ),
    inference(avatar_component_clause,[],[f18489])).

fof(f18489,plain,
    ( spl2_533
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_533])])).

fof(f5635,plain,
    ( ! [X4,X5] : k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4)))) = X4
    | ~ spl2_326 ),
    inference(avatar_component_clause,[],[f5634])).

fof(f5634,plain,
    ( spl2_326
  <=> ! [X5,X4] : k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4)))) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_326])])).

fof(f18492,plain,
    ( spl2_533
    | ~ spl2_4
    | ~ spl2_103
    | ~ spl2_286
    | ~ spl2_485
    | ~ spl2_509 ),
    inference(avatar_split_clause,[],[f18427,f17462,f16572,f4907,f1171,f122,f18489])).

fof(f18427,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_103
    | ~ spl2_286
    | ~ spl2_485
    | ~ spl2_509 ),
    inference(backward_demodulation,[],[f16878,f18426])).

fof(f18426,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_286
    | ~ spl2_509 ),
    inference(forward_demodulation,[],[f18037,f4909])).

fof(f17949,plain,
    ( spl2_524
    | ~ spl2_175
    | ~ spl2_523 ),
    inference(avatar_split_clause,[],[f17943,f17939,f2781,f17946])).

fof(f17939,plain,
    ( spl2_523
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_523])])).

fof(f17943,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_175
    | ~ spl2_523 ),
    inference(superposition,[],[f17941,f2782])).

fof(f17941,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_523 ),
    inference(avatar_component_clause,[],[f17939])).

fof(f17942,plain,
    ( spl2_523
    | ~ spl2_4
    | ~ spl2_501 ),
    inference(avatar_split_clause,[],[f17791,f17181,f122,f17939])).

fof(f17181,plain,
    ( spl2_501
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_501])])).

fof(f17791,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_501 ),
    inference(resolution,[],[f17182,f124])).

fof(f17182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_501 ),
    inference(avatar_component_clause,[],[f17181])).

fof(f17464,plain,
    ( spl2_509
    | ~ spl2_2
    | ~ spl2_395 ),
    inference(avatar_split_clause,[],[f11993,f11288,f113,f17462])).

fof(f11288,plain,
    ( spl2_395
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_395])])).

fof(f11993,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_395 ),
    inference(resolution,[],[f11289,f115])).

fof(f11289,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) )
    | ~ spl2_395 ),
    inference(avatar_component_clause,[],[f11288])).

fof(f17183,plain,
    ( spl2_501
    | ~ spl2_2
    | ~ spl2_383 ),
    inference(avatar_split_clause,[],[f11735,f10965,f113,f17181])).

fof(f10965,plain,
    ( spl2_383
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_383])])).

fof(f11735,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_383 ),
    inference(resolution,[],[f10966,f115])).

fof(f10966,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) )
    | ~ spl2_383 ),
    inference(avatar_component_clause,[],[f10965])).

fof(f16574,plain,
    ( spl2_485
    | ~ spl2_4
    | ~ spl2_336 ),
    inference(avatar_split_clause,[],[f15132,f5736,f122,f16572])).

fof(f5736,plain,
    ( spl2_336
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_336])])).

fof(f15132,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_tarski(k2_tarski(sK1,X2)) = k4_subset_1(u1_struct_0(sK0),sK1,X2) )
    | ~ spl2_4
    | ~ spl2_336 ),
    inference(resolution,[],[f124,f5737])).

fof(f5737,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )
    | ~ spl2_336 ),
    inference(avatar_component_clause,[],[f5736])).

fof(f15618,plain,
    ( spl2_463
    | ~ spl2_173
    | ~ spl2_176 ),
    inference(avatar_split_clause,[],[f15593,f2787,f2754,f15615])).

fof(f2754,plain,
    ( spl2_173
  <=> ! [X1,X0] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_173])])).

fof(f2787,plain,
    ( spl2_176
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).

fof(f15593,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_173
    | ~ spl2_176 ),
    inference(superposition,[],[f2755,f2789])).

fof(f2789,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_176 ),
    inference(avatar_component_clause,[],[f2787])).

fof(f2755,plain,
    ( ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0)
    | ~ spl2_173 ),
    inference(avatar_component_clause,[],[f2754])).

fof(f11988,plain,
    ( spl2_413
    | ~ spl2_7
    | ~ spl2_390 ),
    inference(avatar_split_clause,[],[f11291,f11268,f135,f11986])).

fof(f11291,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)
    | ~ spl2_7
    | ~ spl2_390 ),
    inference(superposition,[],[f11269,f136])).

fof(f11643,plain,
    ( spl2_402
    | ~ spl2_173
    | ~ spl2_289
    | ~ spl2_368
    | ~ spl2_390 ),
    inference(avatar_split_clause,[],[f11441,f11268,f10516,f4950,f2754,f11641])).

fof(f11441,plain,
    ( ! [X50,X49] : k3_subset_1(X49,k7_subset_1(X49,X49,X50)) = k1_setfam_1(k2_tarski(X49,X50))
    | ~ spl2_173
    | ~ spl2_289
    | ~ spl2_368
    | ~ spl2_390 ),
    inference(backward_demodulation,[],[f10544,f11298])).

fof(f11298,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1))
    | ~ spl2_289
    | ~ spl2_390 ),
    inference(superposition,[],[f11269,f4951])).

fof(f10544,plain,
    ( ! [X50,X49] : k3_subset_1(X49,k7_subset_1(X49,X49,X50)) = k7_subset_1(X49,X49,k7_subset_1(X49,X49,X50))
    | ~ spl2_173
    | ~ spl2_368 ),
    inference(resolution,[],[f10517,f2755])).

fof(f11290,plain,(
    spl2_395 ),
    inference(avatar_split_clause,[],[f69,f11288])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f11270,plain,
    ( spl2_390
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f2609,f2292,f497,f11268])).

fof(f497,plain,
    ( spl2_56
  <=> ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f2292,plain,
    ( spl2_151
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).

fof(f2609,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) = k7_subset_1(X3,X3,X4)
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(resolution,[],[f2293,f498])).

fof(f498,plain,
    ( ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f497])).

fof(f2293,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) )
    | ~ spl2_151 ),
    inference(avatar_component_clause,[],[f2292])).

fof(f10971,plain,
    ( spl2_384
    | ~ spl2_41
    | ~ spl2_311 ),
    inference(avatar_split_clause,[],[f5400,f5374,f386,f10969])).

fof(f386,plain,
    ( spl2_41
  <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f5374,plain,
    ( spl2_311
  <=> ! [X1,X0] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_311])])).

fof(f5400,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))
    | ~ spl2_41
    | ~ spl2_311 ),
    inference(superposition,[],[f5375,f387])).

fof(f387,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f386])).

fof(f5375,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)
    | ~ spl2_311 ),
    inference(avatar_component_clause,[],[f5374])).

fof(f10967,plain,(
    spl2_383 ),
    inference(avatar_split_clause,[],[f68,f10965])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f10963,plain,
    ( spl2_382
    | ~ spl2_15
    | ~ spl2_311 ),
    inference(avatar_split_clause,[],[f5377,f5374,f186,f10961])).

fof(f186,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f5377,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X2,X0)),X2),X1) )
    | ~ spl2_15
    | ~ spl2_311 ),
    inference(resolution,[],[f5375,f187])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f186])).

fof(f10922,plain,
    ( spl2_376
    | ~ spl2_131
    | ~ spl2_375 ),
    inference(avatar_split_clause,[],[f10877,f10873,f1558,f10920])).

fof(f10873,plain,
    ( spl2_375
  <=> ! [X1,X0] :
        ( k4_subset_1(X0,k1_xboole_0,X1) = X1
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_375])])).

fof(f10877,plain,
    ( ! [X2,X1] : k4_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0,X1) = X1
    | ~ spl2_131
    | ~ spl2_375 ),
    inference(resolution,[],[f10874,f1559])).

fof(f10874,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | k4_subset_1(X0,k1_xboole_0,X1) = X1 )
    | ~ spl2_375 ),
    inference(avatar_component_clause,[],[f10873])).

fof(f10875,plain,
    ( spl2_375
    | ~ spl2_9
    | ~ spl2_372 ),
    inference(avatar_split_clause,[],[f10853,f10850,f143,f10873])).

fof(f143,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f10850,plain,
    ( spl2_372
  <=> ! [X7,X6] :
        ( k4_subset_1(X7,k1_xboole_0,X6) = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_372])])).

fof(f10853,plain,
    ( ! [X0,X1] :
        ( k4_subset_1(X0,k1_xboole_0,X1) = X1
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_9
    | ~ spl2_372 ),
    inference(resolution,[],[f10851,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f10851,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | k4_subset_1(X7,k1_xboole_0,X6) = X6 )
    | ~ spl2_372 ),
    inference(avatar_component_clause,[],[f10850])).

fof(f10852,plain,
    ( spl2_372
    | ~ spl2_137
    | ~ spl2_336
    | ~ spl2_369 ),
    inference(avatar_split_clause,[],[f10764,f10708,f5736,f2129,f10850])).

fof(f2129,plain,
    ( spl2_137
  <=> ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).

fof(f10708,plain,
    ( spl2_369
  <=> ! [X4] : k3_tarski(k2_tarski(k1_xboole_0,X4)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_369])])).

fof(f10764,plain,
    ( ! [X6,X7] :
        ( k4_subset_1(X7,k1_xboole_0,X6) = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(X7)) )
    | ~ spl2_137
    | ~ spl2_336
    | ~ spl2_369 ),
    inference(forward_demodulation,[],[f10756,f10709])).

fof(f10709,plain,
    ( ! [X4] : k3_tarski(k2_tarski(k1_xboole_0,X4)) = X4
    | ~ spl2_369 ),
    inference(avatar_component_clause,[],[f10708])).

fof(f10756,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | k3_tarski(k2_tarski(k1_xboole_0,X6)) = k4_subset_1(X7,k1_xboole_0,X6) )
    | ~ spl2_137
    | ~ spl2_336 ),
    inference(resolution,[],[f5737,f2130])).

fof(f2130,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ spl2_137 ),
    inference(avatar_component_clause,[],[f2129])).

fof(f10710,plain,
    ( spl2_369
    | ~ spl2_22
    | ~ spl2_135
    | ~ spl2_203
    | ~ spl2_247
    | ~ spl2_368 ),
    inference(avatar_split_clause,[],[f10574,f10516,f4043,f3348,f2116,f227,f10708])).

fof(f2116,plain,
    ( spl2_135
  <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f3348,plain,
    ( spl2_203
  <=> ! [X3,X4] : k1_xboole_0 = k7_subset_1(X3,X3,k3_tarski(k2_tarski(X4,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).

fof(f4043,plain,
    ( spl2_247
  <=> ! [X10] : r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X10)),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_247])])).

fof(f10574,plain,
    ( ! [X4] : k3_tarski(k2_tarski(k1_xboole_0,X4)) = X4
    | ~ spl2_22
    | ~ spl2_135
    | ~ spl2_203
    | ~ spl2_247
    | ~ spl2_368 ),
    inference(forward_demodulation,[],[f10573,f2117])).

fof(f2117,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_135 ),
    inference(avatar_component_clause,[],[f2116])).

fof(f10573,plain,
    ( ! [X4] : k3_subset_1(X4,k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X4))
    | ~ spl2_22
    | ~ spl2_203
    | ~ spl2_247
    | ~ spl2_368 ),
    inference(backward_demodulation,[],[f4051,f10570])).

fof(f10570,plain,
    ( ! [X36] : k1_xboole_0 = k3_subset_1(X36,k3_tarski(k2_tarski(k1_xboole_0,X36)))
    | ~ spl2_203
    | ~ spl2_247
    | ~ spl2_368 ),
    inference(forward_demodulation,[],[f10535,f3349])).

fof(f3349,plain,
    ( ! [X4,X3] : k1_xboole_0 = k7_subset_1(X3,X3,k3_tarski(k2_tarski(X4,X3)))
    | ~ spl2_203 ),
    inference(avatar_component_clause,[],[f3348])).

fof(f10535,plain,
    ( ! [X36] : k3_subset_1(X36,k3_tarski(k2_tarski(k1_xboole_0,X36))) = k7_subset_1(X36,X36,k3_tarski(k2_tarski(k1_xboole_0,X36)))
    | ~ spl2_247
    | ~ spl2_368 ),
    inference(resolution,[],[f10517,f4044])).

fof(f4044,plain,
    ( ! [X10] : r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X10)),X10)
    | ~ spl2_247 ),
    inference(avatar_component_clause,[],[f4043])).

fof(f4051,plain,
    ( ! [X4] : k3_tarski(k2_tarski(k1_xboole_0,X4)) = k3_subset_1(X4,k3_subset_1(X4,k3_tarski(k2_tarski(k1_xboole_0,X4))))
    | ~ spl2_22
    | ~ spl2_247 ),
    inference(resolution,[],[f4044,f228])).

fof(f10518,plain,
    ( spl2_368
    | ~ spl2_9
    | ~ spl2_56
    | ~ spl2_66
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f2649,f2292,f600,f497,f143,f10516])).

fof(f600,plain,
    ( spl2_66
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f2649,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_9
    | ~ spl2_56
    | ~ spl2_66
    | ~ spl2_151 ),
    inference(backward_demodulation,[],[f1227,f2609])).

fof(f1227,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_9
    | ~ spl2_66 ),
    inference(resolution,[],[f601,f144])).

fof(f601,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) )
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f600])).

fof(f5738,plain,(
    spl2_336 ),
    inference(avatar_split_clause,[],[f104,f5736])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f92,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f5636,plain,
    ( spl2_326
    | ~ spl2_56
    | ~ spl2_151
    | ~ spl2_203
    | ~ spl2_234
    | ~ spl2_289 ),
    inference(avatar_split_clause,[],[f5128,f4950,f3814,f3348,f2292,f497,f5634])).

fof(f3814,plain,
    ( spl2_234
  <=> ! [X3] : k7_subset_1(X3,X3,k1_xboole_0) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_234])])).

fof(f5128,plain,
    ( ! [X4,X5] : k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4)))) = X4
    | ~ spl2_56
    | ~ spl2_151
    | ~ spl2_203
    | ~ spl2_234
    | ~ spl2_289 ),
    inference(forward_demodulation,[],[f5127,f3815])).

fof(f3815,plain,
    ( ! [X3] : k7_subset_1(X3,X3,k1_xboole_0) = X3
    | ~ spl2_234 ),
    inference(avatar_component_clause,[],[f3814])).

fof(f5127,plain,
    ( ! [X4,X5] : k7_subset_1(X4,X4,k1_xboole_0) = k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4))))
    | ~ spl2_56
    | ~ spl2_151
    | ~ spl2_203
    | ~ spl2_289 ),
    inference(forward_demodulation,[],[f5111,f2609])).

fof(f5111,plain,
    ( ! [X4,X5] : k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4)))) = k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,k1_xboole_0)))
    | ~ spl2_203
    | ~ spl2_289 ),
    inference(superposition,[],[f4951,f3349])).

fof(f5632,plain,
    ( spl2_325
    | ~ spl2_56
    | ~ spl2_151
    | ~ spl2_202
    | ~ spl2_234
    | ~ spl2_289 ),
    inference(avatar_split_clause,[],[f5125,f4950,f3814,f3344,f2292,f497,f5630])).

fof(f3344,plain,
    ( spl2_202
  <=> ! [X1,X2] : k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_202])])).

fof(f5125,plain,
    ( ! [X2,X3] : k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3)))) = X2
    | ~ spl2_56
    | ~ spl2_151
    | ~ spl2_202
    | ~ spl2_234
    | ~ spl2_289 ),
    inference(forward_demodulation,[],[f5124,f3815])).

fof(f5124,plain,
    ( ! [X2,X3] : k7_subset_1(X2,X2,k1_xboole_0) = k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3))))
    | ~ spl2_56
    | ~ spl2_151
    | ~ spl2_202
    | ~ spl2_289 ),
    inference(forward_demodulation,[],[f5110,f2609])).

fof(f5110,plain,
    ( ! [X2,X3] : k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3)))) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_xboole_0)))
    | ~ spl2_202
    | ~ spl2_289 ),
    inference(superposition,[],[f4951,f3345])).

fof(f3345,plain,
    ( ! [X2,X1] : k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ spl2_202 ),
    inference(avatar_component_clause,[],[f3344])).

fof(f5376,plain,
    ( spl2_311
    | ~ spl2_7
    | ~ spl2_13
    | ~ spl2_56
    | ~ spl2_77
    | ~ spl2_151
    | ~ spl2_202
    | ~ spl2_234
    | ~ spl2_289 ),
    inference(avatar_split_clause,[],[f5126,f4950,f3814,f3344,f2292,f768,f497,f172,f135,f5374])).

fof(f172,plain,
    ( spl2_13
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f768,plain,
    ( spl2_77
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)
        | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f5126,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)
    | ~ spl2_7
    | ~ spl2_13
    | ~ spl2_56
    | ~ spl2_77
    | ~ spl2_151
    | ~ spl2_202
    | ~ spl2_234
    | ~ spl2_289 ),
    inference(backward_demodulation,[],[f1355,f5125])).

fof(f1355,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))),X1)
    | ~ spl2_7
    | ~ spl2_13
    | ~ spl2_77 ),
    inference(forward_demodulation,[],[f1339,f136])).

fof(f1339,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))),X1)
    | ~ spl2_13
    | ~ spl2_77 ),
    inference(resolution,[],[f769,f173])).

fof(f173,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f769,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
        | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) )
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f768])).

fof(f4952,plain,
    ( spl2_289
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f2623,f2292,f497,f4950])).

fof(f2623,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))))
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(backward_demodulation,[],[f97,f2609])).

fof(f97,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f76,f74,f93,f93])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f78,f74])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f4910,plain,
    ( spl2_286
    | ~ spl2_4
    | ~ spl2_34
    | ~ spl2_285 ),
    inference(avatar_split_clause,[],[f4905,f4898,f324,f122,f4907])).

fof(f4898,plain,
    ( spl2_285
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_285])])).

fof(f4905,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_34
    | ~ spl2_285 ),
    inference(subsumption_resolution,[],[f4902,f124])).

fof(f4902,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_34
    | ~ spl2_285 ),
    inference(resolution,[],[f4899,f326])).

fof(f4899,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_285 ),
    inference(avatar_component_clause,[],[f4898])).

fof(f4900,plain,
    ( spl2_285
    | ~ spl2_2
    | ~ spl2_138 ),
    inference(avatar_split_clause,[],[f2428,f2150,f113,f4898])).

fof(f2150,plain,
    ( spl2_138
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).

fof(f2428,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2
    | ~ spl2_138 ),
    inference(resolution,[],[f2151,f115])).

fof(f2151,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl2_138 ),
    inference(avatar_component_clause,[],[f2150])).

fof(f4045,plain,
    ( spl2_247
    | ~ spl2_13
    | ~ spl2_246 ),
    inference(avatar_split_clause,[],[f4006,f3996,f172,f4043])).

fof(f3996,plain,
    ( spl2_246
  <=> ! [X11,X10] :
        ( r1_tarski(X10,X11)
        | ~ r1_tarski(X10,k3_tarski(k2_tarski(k1_xboole_0,X11))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_246])])).

fof(f4006,plain,
    ( ! [X10] : r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X10)),X10)
    | ~ spl2_13
    | ~ spl2_246 ),
    inference(resolution,[],[f3997,f173])).

fof(f3997,plain,
    ( ! [X10,X11] :
        ( ~ r1_tarski(X10,k3_tarski(k2_tarski(k1_xboole_0,X11)))
        | r1_tarski(X10,X11) )
    | ~ spl2_246 ),
    inference(avatar_component_clause,[],[f3996])).

fof(f3998,plain,
    ( spl2_246
    | ~ spl2_213
    | ~ spl2_234 ),
    inference(avatar_split_clause,[],[f3988,f3814,f3482,f3996])).

fof(f3482,plain,
    ( spl2_213
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k7_subset_1(X0,X0,X1),X2)
        | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_213])])).

fof(f3988,plain,
    ( ! [X10,X11] :
        ( r1_tarski(X10,X11)
        | ~ r1_tarski(X10,k3_tarski(k2_tarski(k1_xboole_0,X11))) )
    | ~ spl2_213
    | ~ spl2_234 ),
    inference(superposition,[],[f3483,f3815])).

fof(f3483,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k7_subset_1(X0,X0,X1),X2)
        | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) )
    | ~ spl2_213 ),
    inference(avatar_component_clause,[],[f3482])).

fof(f3816,plain,
    ( spl2_234
    | ~ spl2_135
    | ~ spl2_137
    | ~ spl2_201 ),
    inference(avatar_split_clause,[],[f3812,f3340,f2129,f2116,f3814])).

fof(f3340,plain,
    ( spl2_201
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_201])])).

fof(f3812,plain,
    ( ! [X3] : k7_subset_1(X3,X3,k1_xboole_0) = X3
    | ~ spl2_135
    | ~ spl2_137
    | ~ spl2_201 ),
    inference(forward_demodulation,[],[f3797,f2117])).

fof(f3797,plain,
    ( ! [X3] : k3_subset_1(X3,k1_xboole_0) = k7_subset_1(X3,X3,k1_xboole_0)
    | ~ spl2_137
    | ~ spl2_201 ),
    inference(resolution,[],[f3341,f2130])).

fof(f3341,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )
    | ~ spl2_201 ),
    inference(avatar_component_clause,[],[f3340])).

fof(f3484,plain,
    ( spl2_213
    | ~ spl2_56
    | ~ spl2_77
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f2632,f2292,f768,f497,f3482])).

fof(f2632,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k7_subset_1(X0,X0,X1),X2)
        | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) )
    | ~ spl2_56
    | ~ spl2_77
    | ~ spl2_151 ),
    inference(backward_demodulation,[],[f769,f2609])).

fof(f3350,plain,
    ( spl2_203
    | ~ spl2_130
    | ~ spl2_197 ),
    inference(avatar_split_clause,[],[f3237,f3168,f1523,f3348])).

fof(f1523,plain,
    ( spl2_130
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).

fof(f3168,plain,
    ( spl2_197
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k7_subset_1(X0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_197])])).

fof(f3237,plain,
    ( ! [X4,X3] : k1_xboole_0 = k7_subset_1(X3,X3,k3_tarski(k2_tarski(X4,X3)))
    | ~ spl2_130
    | ~ spl2_197 ),
    inference(resolution,[],[f3169,f1524])).

fof(f1524,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))
    | ~ spl2_130 ),
    inference(avatar_component_clause,[],[f1523])).

fof(f3169,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k7_subset_1(X0,X0,X1) )
    | ~ spl2_197 ),
    inference(avatar_component_clause,[],[f3168])).

fof(f3346,plain,
    ( spl2_202
    | ~ spl2_131
    | ~ spl2_197 ),
    inference(avatar_split_clause,[],[f3236,f3168,f1558,f3344])).

fof(f3236,plain,
    ( ! [X2,X1] : k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2)))
    | ~ spl2_131
    | ~ spl2_197 ),
    inference(resolution,[],[f3169,f1559])).

fof(f3342,plain,
    ( spl2_201
    | ~ spl2_56
    | ~ spl2_66
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f2631,f2292,f600,f497,f3340])).

fof(f2631,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_56
    | ~ spl2_66
    | ~ spl2_151 ),
    inference(backward_demodulation,[],[f601,f2609])).

fof(f3170,plain,
    ( spl2_197
    | ~ spl2_23
    | ~ spl2_193 ),
    inference(avatar_split_clause,[],[f3133,f3042,f241,f3168])).

fof(f241,plain,
    ( spl2_23
  <=> ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f3042,plain,
    ( spl2_193
  <=> ! [X1,X0] :
        ( r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).

fof(f3133,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k7_subset_1(X0,X0,X1) )
    | ~ spl2_23
    | ~ spl2_193 ),
    inference(resolution,[],[f3043,f242])).

fof(f242,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f241])).

fof(f3043,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_193 ),
    inference(avatar_component_clause,[],[f3042])).

fof(f3044,plain,
    ( spl2_193
    | ~ spl2_56
    | ~ spl2_77
    | ~ spl2_151
    | ~ spl2_170 ),
    inference(avatar_split_clause,[],[f2660,f2566,f2292,f768,f497,f3042])).

fof(f2566,plain,
    ( spl2_170
  <=> ! [X1,X0] :
        ( r1_tarski(X1,k3_tarski(k2_tarski(X0,k1_xboole_0)))
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_170])])).

fof(f2660,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_56
    | ~ spl2_77
    | ~ spl2_151
    | ~ spl2_170 ),
    inference(backward_demodulation,[],[f2577,f2609])).

fof(f2577,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_xboole_0) )
    | ~ spl2_77
    | ~ spl2_170 ),
    inference(resolution,[],[f2567,f769])).

fof(f2567,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k3_tarski(k2_tarski(X0,k1_xboole_0)))
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_170 ),
    inference(avatar_component_clause,[],[f2566])).

fof(f2841,plain,
    ( spl2_181
    | ~ spl2_20
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f2625,f2292,f497,f213,f2839])).

fof(f213,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f2625,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k7_subset_1(X1,X1,X0))
        | k1_xboole_0 = X0 )
    | ~ spl2_20
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(backward_demodulation,[],[f214,f2609])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))
        | k1_xboole_0 = X0 )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f2790,plain,
    ( spl2_176
    | ~ spl2_35
    | ~ spl2_175 ),
    inference(avatar_split_clause,[],[f2784,f2781,f328,f2787])).

fof(f328,plain,
    ( spl2_35
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f2784,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_35
    | ~ spl2_175 ),
    inference(superposition,[],[f2782,f330])).

fof(f330,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f328])).

fof(f2783,plain,
    ( spl2_175
    | ~ spl2_4
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f2743,f2292,f497,f122,f2781])).

fof(f2743,plain,
    ( ! [X21] : k7_subset_1(u1_struct_0(sK0),sK1,X21) = k7_subset_1(sK1,sK1,X21)
    | ~ spl2_4
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(forward_demodulation,[],[f2622,f2609])).

fof(f2622,plain,
    ( ! [X21] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X21))) = k7_subset_1(u1_struct_0(sK0),sK1,X21)
    | ~ spl2_4
    | ~ spl2_151 ),
    inference(resolution,[],[f2293,f124])).

fof(f2756,plain,
    ( spl2_173
    | ~ spl2_12
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(avatar_split_clause,[],[f2624,f2292,f497,f162,f2754])).

fof(f162,plain,
    ( spl2_12
  <=> ! [X1,X0] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f2624,plain,
    ( ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0)
    | ~ spl2_12
    | ~ spl2_56
    | ~ spl2_151 ),
    inference(backward_demodulation,[],[f163,f2609])).

fof(f163,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f2568,plain,
    ( spl2_170
    | ~ spl2_7
    | ~ spl2_167 ),
    inference(avatar_split_clause,[],[f2548,f2523,f135,f2566])).

fof(f2523,plain,
    ( spl2_167
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_167])])).

fof(f2548,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k3_tarski(k2_tarski(X0,k1_xboole_0)))
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_7
    | ~ spl2_167 ),
    inference(superposition,[],[f2524,f136])).

fof(f2524,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,X1)))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_167 ),
    inference(avatar_component_clause,[],[f2523])).

fof(f2525,plain,
    ( spl2_167
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f1490,f902,f131,f127,f2523])).

fof(f127,plain,
    ( spl2_5
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f131,plain,
    ( spl2_6
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f902,plain,
    ( spl2_88
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
        | ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f1490,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,X1))) )
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_88 ),
    inference(forward_demodulation,[],[f1487,f128])).

fof(f128,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1487,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k5_xboole_0(X0,k1_xboole_0),X1)
        | r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,X1))) )
    | ~ spl2_6
    | ~ spl2_88 ),
    inference(superposition,[],[f903,f132])).

fof(f132,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f903,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)
        | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) )
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f902])).

fof(f2294,plain,(
    spl2_151 ),
    inference(avatar_split_clause,[],[f101,f2292])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f88,f93])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f2152,plain,(
    spl2_138 ),
    inference(avatar_split_clause,[],[f70,f2150])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f2131,plain,
    ( spl2_137
    | ~ spl2_17
    | ~ spl2_56
    | ~ spl2_136 ),
    inference(avatar_split_clause,[],[f2127,f2122,f497,f199,f2129])).

fof(f199,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f2122,plain,
    ( spl2_136
  <=> ! [X18] : k1_xboole_0 = k3_subset_1(X18,X18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).

fof(f2127,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ spl2_17
    | ~ spl2_56
    | ~ spl2_136 ),
    inference(subsumption_resolution,[],[f2126,f498])).

fof(f2126,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) )
    | ~ spl2_17
    | ~ spl2_136 ),
    inference(superposition,[],[f200,f2123])).

fof(f2123,plain,
    ( ! [X18] : k1_xboole_0 = k3_subset_1(X18,X18)
    | ~ spl2_136 ),
    inference(avatar_component_clause,[],[f2122])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f199])).

fof(f2124,plain,
    ( spl2_136
    | ~ spl2_20
    | ~ spl2_132 ),
    inference(avatar_split_clause,[],[f1605,f1595,f213,f2122])).

fof(f1595,plain,
    ( spl2_132
  <=> ! [X1,X0] : r1_tarski(k3_subset_1(X0,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).

fof(f1605,plain,
    ( ! [X18] : k1_xboole_0 = k3_subset_1(X18,X18)
    | ~ spl2_20
    | ~ spl2_132 ),
    inference(resolution,[],[f1596,f214])).

fof(f1596,plain,
    ( ! [X0,X1] : r1_tarski(k3_subset_1(X0,X0),X1)
    | ~ spl2_132 ),
    inference(avatar_component_clause,[],[f1595])).

fof(f2118,plain,
    ( spl2_135
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_132 ),
    inference(avatar_split_clause,[],[f1622,f1595,f251,f213,f2116])).

fof(f251,plain,
    ( spl2_24
  <=> ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1622,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_132 ),
    inference(backward_demodulation,[],[f252,f1605])).

fof(f252,plain,
    ( ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f251])).

fof(f1597,plain,
    ( spl2_132
    | ~ spl2_77
    | ~ spl2_121
    | ~ spl2_131 ),
    inference(avatar_split_clause,[],[f1592,f1558,f1389,f768,f1595])).

fof(f1389,plain,
    ( spl2_121
  <=> ! [X2] : k3_subset_1(X2,X2) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).

fof(f1592,plain,
    ( ! [X0,X1] : r1_tarski(k3_subset_1(X0,X0),X1)
    | ~ spl2_77
    | ~ spl2_121
    | ~ spl2_131 ),
    inference(forward_demodulation,[],[f1561,f1390])).

fof(f1390,plain,
    ( ! [X2] : k3_subset_1(X2,X2) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))
    | ~ spl2_121 ),
    inference(avatar_component_clause,[],[f1389])).

fof(f1561,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))),X1)
    | ~ spl2_77
    | ~ spl2_131 ),
    inference(resolution,[],[f1559,f769])).

fof(f1560,plain,
    ( spl2_131
    | ~ spl2_7
    | ~ spl2_130 ),
    inference(avatar_split_clause,[],[f1553,f1523,f135,f1558])).

fof(f1553,plain,
    ( ! [X0,X1] : r1_tarski(X1,k3_tarski(k2_tarski(X1,X0)))
    | ~ spl2_7
    | ~ spl2_130 ),
    inference(superposition,[],[f1524,f136])).

fof(f1525,plain,
    ( spl2_130
    | ~ spl2_12
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f1474,f902,f162,f1523])).

fof(f1474,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))
    | ~ spl2_12
    | ~ spl2_88 ),
    inference(resolution,[],[f903,f163])).

fof(f1391,plain,
    ( spl2_121
    | ~ spl2_56
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f1228,f600,f497,f1389])).

fof(f1228,plain,
    ( ! [X2] : k3_subset_1(X2,X2) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))
    | ~ spl2_56
    | ~ spl2_66 ),
    inference(resolution,[],[f601,f498])).

fof(f1174,plain,
    ( spl2_103
    | ~ spl2_4
    | ~ spl2_102 ),
    inference(avatar_split_clause,[],[f1166,f1163,f122,f1171])).

fof(f1163,plain,
    ( spl2_102
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).

fof(f1166,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_102 ),
    inference(resolution,[],[f1164,f124])).

fof(f1164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_102 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f1165,plain,
    ( spl2_102
    | ~ spl2_2
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f1161,f484,f113,f1163])).

fof(f484,plain,
    ( spl2_55
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f1161,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2
    | ~ spl2_55 ),
    inference(resolution,[],[f485,f115])).

fof(f485,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f484])).

fof(f904,plain,(
    spl2_88 ),
    inference(avatar_split_clause,[],[f103,f902])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ) ),
    inference(definition_unfolding,[],[f90,f75,f93])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f770,plain,(
    spl2_77 ),
    inference(avatar_split_clause,[],[f102,f768])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f89,f93,f75])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f602,plain,(
    spl2_66 ),
    inference(avatar_split_clause,[],[f99,f600])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f80,f93])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f499,plain,
    ( spl2_56
    | ~ spl2_13
    | ~ spl2_29
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f495,f480,f290,f172,f497])).

fof(f290,plain,
    ( spl2_29
  <=> ! [X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ r1_tarski(k3_subset_1(X1,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f480,plain,
    ( spl2_54
  <=> ! [X1,X0] :
        ( r1_tarski(k3_subset_1(X0,X0),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f495,plain,
    ( ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ spl2_13
    | ~ spl2_29
    | ~ spl2_54 ),
    inference(subsumption_resolution,[],[f291,f487])).

fof(f487,plain,
    ( ! [X0] : r1_tarski(k3_subset_1(X0,X0),X0)
    | ~ spl2_13
    | ~ spl2_54 ),
    inference(resolution,[],[f481,f173])).

fof(f481,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k3_subset_1(X0,X0),X1) )
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f480])).

fof(f291,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k3_subset_1(X1,X1),X1)
        | m1_subset_1(X1,k1_zfmisc_1(X1)) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f290])).

fof(f486,plain,(
    spl2_55 ),
    inference(avatar_split_clause,[],[f85,f484])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f482,plain,
    ( spl2_54
    | ~ spl2_13
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f470,f467,f172,f480])).

fof(f467,plain,
    ( spl2_53
  <=> ! [X1,X3,X2] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k3_subset_1(X1,X3),X2)
        | ~ r1_tarski(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f470,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_subset_1(X0,X0),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13
    | ~ spl2_53 ),
    inference(resolution,[],[f468,f173])).

fof(f468,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X3,X1)
        | r1_tarski(k3_subset_1(X1,X3),X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f467])).

fof(f469,plain,
    ( spl2_53
    | ~ spl2_9
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f443,f439,f143,f467])).

fof(f439,plain,
    ( spl2_49
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X1,X2)
        | r1_tarski(k3_subset_1(X1,X0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f443,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k3_subset_1(X1,X3),X2)
        | ~ r1_tarski(X3,X1) )
    | ~ spl2_9
    | ~ spl2_49 ),
    inference(resolution,[],[f440,f144])).

fof(f440,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X1,X2)
        | r1_tarski(k3_subset_1(X1,X0),X2) )
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f439])).

fof(f441,plain,
    ( spl2_49
    | ~ spl2_15
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f207,f204,f186,f439])).

fof(f204,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(k3_subset_1(X1,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X1,X2)
        | r1_tarski(k3_subset_1(X1,X0),X2) )
    | ~ spl2_15
    | ~ spl2_18 ),
    inference(resolution,[],[f205,f187])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_subset_1(X1,X0),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f411,plain,
    ( spl2_45
    | ~ spl2_9
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f397,f390,f143,f409])).

fof(f390,plain,
    ( spl2_42
  <=> ! [X1,X0] :
        ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f397,plain,
    ( ! [X0,X1] :
        ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_9
    | ~ spl2_42 ),
    inference(resolution,[],[f391,f144])).

fof(f391,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 )
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f390])).

fof(f407,plain,(
    spl2_44 ),
    inference(avatar_split_clause,[],[f84,f405])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f392,plain,(
    spl2_42 ),
    inference(avatar_split_clause,[],[f106,f390])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f82,f64])).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f388,plain,(
    spl2_41 ),
    inference(avatar_split_clause,[],[f98,f386])).

fof(f98,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f77,f75,f75,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f331,plain,
    ( spl2_34
    | spl2_35 ),
    inference(avatar_split_clause,[],[f62,f328,f324])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f292,plain,
    ( spl2_29
    | ~ spl2_9
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f287,f283,f143,f290])).

fof(f283,plain,
    ( spl2_28
  <=> ! [X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f287,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ r1_tarski(k3_subset_1(X1,X1),X1) )
    | ~ spl2_9
    | ~ spl2_28 ),
    inference(resolution,[],[f284,f144])).

fof(f284,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))
        | m1_subset_1(X1,k1_zfmisc_1(X1)) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f283])).

fof(f285,plain,
    ( spl2_28
    | ~ spl2_17
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f255,f251,f199,f283])).

fof(f255,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) )
    | ~ spl2_17
    | ~ spl2_24 ),
    inference(superposition,[],[f200,f252])).

fof(f253,plain,
    ( spl2_24
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f230,f227,f172,f251])).

fof(f230,plain,
    ( ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(resolution,[],[f228,f173])).

fof(f243,plain,
    ( spl2_23
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f239,f213,f149,f127,f241])).

fof(f149,plain,
    ( spl2_10
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f239,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f238,f128])).

fof(f238,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | k1_xboole_0 = X1 )
    | ~ spl2_10
    | ~ spl2_20 ),
    inference(superposition,[],[f214,f150])).

fof(f150,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f229,plain,
    ( spl2_22
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f217,f209,f143,f227])).

fof(f209,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(resolution,[],[f210,f144])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f209])).

fof(f215,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f100,f213])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ) ),
    inference(definition_unfolding,[],[f83,f93])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f211,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f81,f209])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f206,plain,
    ( spl2_18
    | ~ spl2_8
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f202,f199,f139,f204])).

fof(f139,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(k3_subset_1(X1,X0),X1) )
    | ~ spl2_8
    | ~ spl2_17 ),
    inference(resolution,[],[f200,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f201,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f79,f199])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f188,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f91,f186])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f174,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f169,f162,f131,f127,f172])).

fof(f169,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f167,f128])).

fof(f167,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(superposition,[],[f163,f132])).

fof(f164,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f96,f162])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f72,f93])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f151,plain,
    ( spl2_10
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f146,f135,f131,f149])).

fof(f146,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f132,f136])).

fof(f145,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f87,f143])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f141,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f86,f139])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f137,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f73,f135])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f133,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f94,f131])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f129,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f105,f127])).

fof(f105,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f95,f94])).

fof(f95,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f66,f93])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f125,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f61,f122])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f116,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f60,f113])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f111,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f59,f108])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:02:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (809795584)
% 0.14/0.37  ipcrm: permission denied for id (809828354)
% 0.14/0.37  ipcrm: permission denied for id (809861123)
% 0.14/0.37  ipcrm: permission denied for id (809893892)
% 0.14/0.37  ipcrm: permission denied for id (809959430)
% 0.14/0.38  ipcrm: permission denied for id (809992200)
% 0.14/0.38  ipcrm: permission denied for id (810057738)
% 0.14/0.38  ipcrm: permission denied for id (810123276)
% 0.14/0.38  ipcrm: permission denied for id (810156045)
% 0.21/0.38  ipcrm: permission denied for id (810254351)
% 0.21/0.39  ipcrm: permission denied for id (810287120)
% 0.21/0.39  ipcrm: permission denied for id (810352658)
% 0.21/0.39  ipcrm: permission denied for id (810385427)
% 0.21/0.39  ipcrm: permission denied for id (810418196)
% 0.21/0.39  ipcrm: permission denied for id (810483734)
% 0.21/0.40  ipcrm: permission denied for id (810680348)
% 0.21/0.40  ipcrm: permission denied for id (810713117)
% 0.21/0.40  ipcrm: permission denied for id (810745886)
% 0.21/0.40  ipcrm: permission denied for id (810778655)
% 0.21/0.41  ipcrm: permission denied for id (810811424)
% 0.21/0.41  ipcrm: permission denied for id (810876963)
% 0.21/0.41  ipcrm: permission denied for id (810942501)
% 0.21/0.41  ipcrm: permission denied for id (810975270)
% 0.21/0.42  ipcrm: permission denied for id (811073577)
% 0.21/0.42  ipcrm: permission denied for id (811106347)
% 0.21/0.42  ipcrm: permission denied for id (811139116)
% 0.21/0.42  ipcrm: permission denied for id (811204655)
% 0.21/0.43  ipcrm: permission denied for id (811368500)
% 0.21/0.43  ipcrm: permission denied for id (811434038)
% 0.21/0.44  ipcrm: permission denied for id (811565114)
% 0.21/0.44  ipcrm: permission denied for id (811761728)
% 0.21/0.45  ipcrm: permission denied for id (811827266)
% 0.21/0.45  ipcrm: permission denied for id (811860035)
% 0.21/0.45  ipcrm: permission denied for id (811892804)
% 0.21/0.45  ipcrm: permission denied for id (811991112)
% 0.21/0.46  ipcrm: permission denied for id (812056650)
% 0.21/0.46  ipcrm: permission denied for id (812122188)
% 0.21/0.46  ipcrm: permission denied for id (812154957)
% 0.21/0.46  ipcrm: permission denied for id (812187726)
% 0.21/0.46  ipcrm: permission denied for id (812220495)
% 0.21/0.46  ipcrm: permission denied for id (812253264)
% 0.21/0.46  ipcrm: permission denied for id (812286033)
% 0.21/0.47  ipcrm: permission denied for id (812351571)
% 0.21/0.47  ipcrm: permission denied for id (812384340)
% 0.21/0.47  ipcrm: permission denied for id (812449878)
% 0.21/0.47  ipcrm: permission denied for id (812515416)
% 0.21/0.47  ipcrm: permission denied for id (812613722)
% 0.21/0.48  ipcrm: permission denied for id (812646491)
% 0.21/0.49  ipcrm: permission denied for id (812941412)
% 0.21/0.49  ipcrm: permission denied for id (813105256)
% 0.21/0.51  ipcrm: permission denied for id (813367410)
% 0.21/0.51  ipcrm: permission denied for id (813400179)
% 0.21/0.51  ipcrm: permission denied for id (813432949)
% 0.21/0.51  ipcrm: permission denied for id (813465718)
% 0.21/0.52  ipcrm: permission denied for id (813695103)
% 0.38/0.62  % (9214)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.38/0.64  % (9206)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.38/0.65  % (9203)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.38/0.65  % (9213)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.38/0.66  % (9212)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.38/0.67  % (9207)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.38/0.67  % (9216)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.38/0.68  % (9208)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.38/0.68  % (9215)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.38/0.71  % (9204)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.38/0.71  % (9202)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.38/0.71  % (9217)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.38/0.72  % (9209)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.38/0.72  % (9210)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.38/0.72  % (9205)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.38/0.73  % (9219)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.38/0.73  % (9218)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.38/0.74  % (9211)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 5.24/1.18  % (9206)Time limit reached!
% 5.24/1.18  % (9206)------------------------------
% 5.24/1.18  % (9206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.24/1.18  % (9206)Termination reason: Time limit
% 5.24/1.18  % (9206)Termination phase: Saturation
% 5.24/1.18  
% 5.24/1.18  % (9206)Memory used [KB]: 11769
% 5.24/1.18  % (9206)Time elapsed: 0.600 s
% 5.24/1.18  % (9206)------------------------------
% 5.24/1.18  % (9206)------------------------------
% 13.31/2.19  % (9208)Time limit reached!
% 13.31/2.19  % (9208)------------------------------
% 13.31/2.19  % (9208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.31/2.19  % (9208)Termination reason: Time limit
% 13.31/2.19  
% 13.31/2.19  % (9208)Memory used [KB]: 33389
% 13.31/2.19  % (9208)Time elapsed: 1.516 s
% 13.31/2.19  % (9208)------------------------------
% 13.31/2.19  % (9208)------------------------------
% 14.78/2.37  % (9207)Time limit reached!
% 14.78/2.37  % (9207)------------------------------
% 14.78/2.37  % (9207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.78/2.37  % (9207)Termination reason: Time limit
% 14.78/2.37  % (9207)Termination phase: Saturation
% 14.78/2.37  
% 14.78/2.37  % (9207)Memory used [KB]: 48997
% 14.78/2.37  % (9207)Time elapsed: 1.500 s
% 14.78/2.37  % (9207)------------------------------
% 14.78/2.37  % (9207)------------------------------
% 14.78/2.40  % (9204)Time limit reached!
% 14.78/2.40  % (9204)------------------------------
% 14.78/2.40  % (9204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.78/2.40  % (9204)Termination reason: Time limit
% 14.78/2.40  
% 14.78/2.40  % (9204)Memory used [KB]: 16119
% 14.78/2.40  % (9204)Time elapsed: 1.809 s
% 14.78/2.40  % (9204)------------------------------
% 14.78/2.40  % (9204)------------------------------
% 18.16/2.82  % (9214)Time limit reached!
% 18.16/2.82  % (9214)------------------------------
% 18.16/2.82  % (9214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.16/2.82  % (9214)Termination reason: Time limit
% 18.16/2.82  % (9214)Termination phase: Saturation
% 18.16/2.82  
% 18.16/2.82  % (9214)Memory used [KB]: 41705
% 18.16/2.82  % (9214)Time elapsed: 2.200 s
% 18.16/2.82  % (9214)------------------------------
% 18.16/2.82  % (9214)------------------------------
% 37.20/5.20  % (9209)Refutation found. Thanks to Tanya!
% 37.20/5.20  % SZS status Theorem for theBenchmark
% 37.20/5.20  % SZS output start Proof for theBenchmark
% 37.20/5.20  fof(f81455,plain,(
% 37.20/5.20    $false),
% 37.20/5.20    inference(avatar_sat_refutation,[],[f111,f116,f125,f129,f133,f137,f141,f145,f151,f164,f174,f188,f201,f206,f211,f215,f229,f243,f253,f285,f292,f331,f388,f392,f407,f411,f441,f469,f482,f486,f499,f602,f770,f904,f1165,f1174,f1391,f1525,f1560,f1597,f2118,f2124,f2131,f2152,f2294,f2525,f2568,f2756,f2783,f2790,f2841,f3044,f3170,f3342,f3346,f3350,f3484,f3816,f3998,f4045,f4900,f4910,f4952,f5376,f5632,f5636,f5738,f10518,f10710,f10852,f10875,f10922,f10963,f10967,f10971,f11270,f11290,f11643,f11988,f15618,f16574,f17183,f17464,f17942,f17949,f18492,f18709,f19247,f19307,f19518,f19540,f19583,f23327,f23375,f73289,f73294,f77178,f81454])).
% 37.20/5.20  fof(f81454,plain,(
% 37.20/5.20    ~spl2_1 | ~spl2_2 | ~spl2_4 | spl2_34 | ~spl2_44 | ~spl2_286),
% 37.20/5.20    inference(avatar_contradiction_clause,[],[f81453])).
% 37.20/5.20  fof(f81453,plain,(
% 37.20/5.20    $false | (~spl2_1 | ~spl2_2 | ~spl2_4 | spl2_34 | ~spl2_44 | ~spl2_286)),
% 37.20/5.20    inference(subsumption_resolution,[],[f81452,f110])).
% 37.20/5.20  fof(f110,plain,(
% 37.20/5.20    v2_pre_topc(sK0) | ~spl2_1),
% 37.20/5.20    inference(avatar_component_clause,[],[f108])).
% 37.20/5.20  fof(f108,plain,(
% 37.20/5.20    spl2_1 <=> v2_pre_topc(sK0)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 37.20/5.20  fof(f81452,plain,(
% 37.20/5.20    ~v2_pre_topc(sK0) | (~spl2_2 | ~spl2_4 | spl2_34 | ~spl2_44 | ~spl2_286)),
% 37.20/5.20    inference(subsumption_resolution,[],[f81451,f115])).
% 37.20/5.20  fof(f115,plain,(
% 37.20/5.20    l1_pre_topc(sK0) | ~spl2_2),
% 37.20/5.20    inference(avatar_component_clause,[],[f113])).
% 37.20/5.20  fof(f113,plain,(
% 37.20/5.20    spl2_2 <=> l1_pre_topc(sK0)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 37.20/5.20  fof(f81451,plain,(
% 37.20/5.20    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_4 | spl2_34 | ~spl2_44 | ~spl2_286)),
% 37.20/5.20    inference(subsumption_resolution,[],[f81450,f124])).
% 37.20/5.20  fof(f124,plain,(
% 37.20/5.20    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 37.20/5.20    inference(avatar_component_clause,[],[f122])).
% 37.20/5.20  fof(f122,plain,(
% 37.20/5.20    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 37.20/5.20  fof(f81450,plain,(
% 37.20/5.20    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_34 | ~spl2_44 | ~spl2_286)),
% 37.20/5.20    inference(subsumption_resolution,[],[f81442,f325])).
% 37.20/5.20  fof(f325,plain,(
% 37.20/5.20    ~v4_pre_topc(sK1,sK0) | spl2_34),
% 37.20/5.20    inference(avatar_component_clause,[],[f324])).
% 37.20/5.20  fof(f324,plain,(
% 37.20/5.20    spl2_34 <=> v4_pre_topc(sK1,sK0)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 37.20/5.20  fof(f81442,plain,(
% 37.20/5.20    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_44 | ~spl2_286)),
% 37.20/5.20    inference(superposition,[],[f406,f4909])).
% 37.20/5.20  fof(f4909,plain,(
% 37.20/5.20    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_286),
% 37.20/5.20    inference(avatar_component_clause,[],[f4907])).
% 37.20/5.20  fof(f4907,plain,(
% 37.20/5.20    spl2_286 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_286])])).
% 37.20/5.20  fof(f406,plain,(
% 37.20/5.20    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_44),
% 37.20/5.20    inference(avatar_component_clause,[],[f405])).
% 37.20/5.20  fof(f405,plain,(
% 37.20/5.20    spl2_44 <=> ! [X1,X0] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 37.20/5.20  fof(f77178,plain,(
% 37.20/5.20    ~spl2_181 | spl2_286 | ~spl2_573 | ~spl2_740 | ~spl2_1596 | ~spl2_1597),
% 37.20/5.20    inference(avatar_contradiction_clause,[],[f77177])).
% 37.20/5.20  fof(f77177,plain,(
% 37.20/5.20    $false | (~spl2_181 | spl2_286 | ~spl2_573 | ~spl2_740 | ~spl2_1596 | ~spl2_1597)),
% 37.20/5.20    inference(subsumption_resolution,[],[f77176,f4908])).
% 37.20/5.20  fof(f4908,plain,(
% 37.20/5.20    sK1 != k2_pre_topc(sK0,sK1) | spl2_286),
% 37.20/5.20    inference(avatar_component_clause,[],[f4907])).
% 37.20/5.20  fof(f77176,plain,(
% 37.20/5.20    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_181 | ~spl2_573 | ~spl2_740 | ~spl2_1596 | ~spl2_1597)),
% 37.20/5.20    inference(forward_demodulation,[],[f75563,f19539])).
% 37.20/5.20  fof(f19539,plain,(
% 37.20/5.20    sK1 = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,sK1) | ~spl2_573),
% 37.20/5.20    inference(avatar_component_clause,[],[f19537])).
% 37.20/5.20  fof(f19537,plain,(
% 37.20/5.20    spl2_573 <=> sK1 = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,sK1)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_573])])).
% 37.20/5.20  fof(f75563,plain,(
% 37.20/5.20    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,sK1) | (~spl2_181 | ~spl2_740 | ~spl2_1596 | ~spl2_1597)),
% 37.20/5.20    inference(backward_demodulation,[],[f73288,f74373])).
% 37.20/5.20  fof(f74373,plain,(
% 37.20/5.20    k1_xboole_0 = k5_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_181 | ~spl2_740 | ~spl2_1597)),
% 37.20/5.20    inference(subsumption_resolution,[],[f74343,f23374])).
% 37.20/5.20  fof(f23374,plain,(
% 37.20/5.20    r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | ~spl2_740),
% 37.20/5.20    inference(avatar_component_clause,[],[f23372])).
% 37.20/5.20  fof(f23372,plain,(
% 37.20/5.20    spl2_740 <=> r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_740])])).
% 37.20/5.20  fof(f74343,plain,(
% 37.20/5.20    ~r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | k1_xboole_0 = k5_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_181 | ~spl2_1597)),
% 37.20/5.20    inference(superposition,[],[f2840,f73293])).
% 37.20/5.20  fof(f73293,plain,(
% 37.20/5.20    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_1597),
% 37.20/5.20    inference(avatar_component_clause,[],[f73291])).
% 37.20/5.20  fof(f73291,plain,(
% 37.20/5.20    spl2_1597 <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_1597])])).
% 37.20/5.20  fof(f2840,plain,(
% 37.20/5.20    ( ! [X0,X1] : (~r1_tarski(X0,k7_subset_1(X1,X1,X0)) | k1_xboole_0 = X0) ) | ~spl2_181),
% 37.20/5.20    inference(avatar_component_clause,[],[f2839])).
% 37.20/5.20  fof(f2839,plain,(
% 37.20/5.20    spl2_181 <=> ! [X1,X0] : (~r1_tarski(X0,k7_subset_1(X1,X1,X0)) | k1_xboole_0 = X0)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).
% 37.20/5.20  fof(f73288,plain,(
% 37.20/5.20    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | ~spl2_1596),
% 37.20/5.20    inference(avatar_component_clause,[],[f73286])).
% 37.20/5.20  fof(f73286,plain,(
% 37.20/5.20    spl2_1596 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_1596])])).
% 37.20/5.20  fof(f73294,plain,(
% 37.20/5.20    spl2_1597 | ~spl2_22 | ~spl2_368 | ~spl2_413 | ~spl2_562 | ~spl2_572 | ~spl2_576),
% 37.20/5.20    inference(avatar_split_clause,[],[f19626,f19580,f19515,f19304,f11986,f10516,f227,f73291])).
% 37.20/5.20  fof(f227,plain,(
% 37.20/5.20    spl2_22 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~r1_tarski(X1,X0))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 37.20/5.20  fof(f10516,plain,(
% 37.20/5.20    spl2_368 <=> ! [X1,X0] : (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) | ~r1_tarski(X1,X0))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_368])])).
% 37.20/5.20  fof(f11986,plain,(
% 37.20/5.20    spl2_413 <=> ! [X1,X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_413])])).
% 37.20/5.20  fof(f19304,plain,(
% 37.20/5.20    spl2_562 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_562])])).
% 37.20/5.20  fof(f19515,plain,(
% 37.20/5.20    spl2_572 <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_572])])).
% 37.20/5.20  fof(f19580,plain,(
% 37.20/5.20    spl2_576 <=> r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_576])])).
% 37.20/5.20  fof(f19626,plain,(
% 37.20/5.20    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | (~spl2_22 | ~spl2_368 | ~spl2_413 | ~spl2_562 | ~spl2_572 | ~spl2_576)),
% 37.20/5.20    inference(forward_demodulation,[],[f19618,f19534])).
% 37.20/5.20  fof(f19534,plain,(
% 37.20/5.20    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | (~spl2_22 | ~spl2_368 | ~spl2_413 | ~spl2_562 | ~spl2_572)),
% 37.20/5.20    inference(backward_demodulation,[],[f19311,f19531])).
% 37.20/5.20  fof(f19531,plain,(
% 37.20/5.20    k5_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | (~spl2_368 | ~spl2_413 | ~spl2_562 | ~spl2_572)),
% 37.20/5.20    inference(backward_demodulation,[],[f19315,f19527])).
% 37.20/5.20  fof(f19527,plain,(
% 37.20/5.20    k5_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),sK1) | (~spl2_413 | ~spl2_572)),
% 37.20/5.20    inference(superposition,[],[f11987,f19517])).
% 37.20/5.20  fof(f19517,plain,(
% 37.20/5.20    sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_572),
% 37.20/5.20    inference(avatar_component_clause,[],[f19515])).
% 37.20/5.20  fof(f11987,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)) ) | ~spl2_413),
% 37.20/5.20    inference(avatar_component_clause,[],[f11986])).
% 37.20/5.20  fof(f19315,plain,(
% 37.20/5.20    k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),sK1) | (~spl2_368 | ~spl2_562)),
% 37.20/5.20    inference(resolution,[],[f19306,f10517])).
% 37.20/5.20  fof(f10517,plain,(
% 37.20/5.20    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) ) | ~spl2_368),
% 37.20/5.20    inference(avatar_component_clause,[],[f10516])).
% 37.20/5.20  fof(f19306,plain,(
% 37.20/5.20    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_562),
% 37.20/5.20    inference(avatar_component_clause,[],[f19304])).
% 37.20/5.20  fof(f19311,plain,(
% 37.20/5.20    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | (~spl2_22 | ~spl2_562)),
% 37.20/5.20    inference(resolution,[],[f19306,f228])).
% 37.20/5.20  fof(f228,plain,(
% 37.20/5.20    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl2_22),
% 37.20/5.20    inference(avatar_component_clause,[],[f227])).
% 37.20/5.20  fof(f19618,plain,(
% 37.20/5.20    k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | (~spl2_368 | ~spl2_576)),
% 37.20/5.20    inference(resolution,[],[f19582,f10517])).
% 37.20/5.20  fof(f19582,plain,(
% 37.20/5.20    r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1)) | ~spl2_576),
% 37.20/5.20    inference(avatar_component_clause,[],[f19580])).
% 37.20/5.20  fof(f73289,plain,(
% 37.20/5.20    spl2_1596 | ~spl2_22 | ~spl2_45 | ~spl2_368 | ~spl2_413 | ~spl2_562 | ~spl2_572 | ~spl2_576),
% 37.20/5.20    inference(avatar_split_clause,[],[f19624,f19580,f19515,f19304,f11986,f10516,f409,f227,f73286])).
% 37.20/5.20  fof(f409,plain,(
% 37.20/5.20    spl2_45 <=> ! [X1,X0] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~r1_tarski(X1,X0))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 37.20/5.20  fof(f19624,plain,(
% 37.20/5.20    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | (~spl2_22 | ~spl2_45 | ~spl2_368 | ~spl2_413 | ~spl2_562 | ~spl2_572 | ~spl2_576)),
% 37.20/5.20    inference(forward_demodulation,[],[f19615,f19534])).
% 37.20/5.20  fof(f19615,plain,(
% 37.20/5.20    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),sK1))) | (~spl2_45 | ~spl2_576)),
% 37.20/5.20    inference(resolution,[],[f19582,f410])).
% 37.20/5.20  fof(f410,plain,(
% 37.20/5.20    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) ) | ~spl2_45),
% 37.20/5.20    inference(avatar_component_clause,[],[f409])).
% 37.20/5.20  fof(f23375,plain,(
% 37.20/5.20    spl2_740 | ~spl2_463 | ~spl2_738),
% 37.20/5.20    inference(avatar_split_clause,[],[f23357,f23325,f15615,f23372])).
% 37.20/5.20  fof(f15615,plain,(
% 37.20/5.20    spl2_463 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_463])])).
% 37.20/5.20  fof(f23325,plain,(
% 37.20/5.20    spl2_738 <=> ! [X11] : (r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),X11) | ~r1_tarski(k2_tops_1(sK0,sK1),X11))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_738])])).
% 37.20/5.20  fof(f23357,plain,(
% 37.20/5.20    r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | (~spl2_463 | ~spl2_738)),
% 37.20/5.20    inference(resolution,[],[f23326,f15617])).
% 37.20/5.20  fof(f15617,plain,(
% 37.20/5.20    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_463),
% 37.20/5.20    inference(avatar_component_clause,[],[f15615])).
% 37.20/5.20  fof(f23326,plain,(
% 37.20/5.20    ( ! [X11] : (~r1_tarski(k2_tops_1(sK0,sK1),X11) | r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),X11)) ) | ~spl2_738),
% 37.20/5.20    inference(avatar_component_clause,[],[f23325])).
% 37.20/5.20  fof(f23327,plain,(
% 37.20/5.20    spl2_738 | ~spl2_382 | ~spl2_560),
% 37.20/5.20    inference(avatar_split_clause,[],[f19283,f19244,f10961,f23325])).
% 37.20/5.20  fof(f10961,plain,(
% 37.20/5.20    spl2_382 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X2,X0)),X2),X1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_382])])).
% 37.20/5.20  fof(f19244,plain,(
% 37.20/5.20    spl2_560 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_560])])).
% 37.20/5.20  fof(f19283,plain,(
% 37.20/5.20    ( ! [X11] : (r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),X11) | ~r1_tarski(k2_tops_1(sK0,sK1),X11)) ) | (~spl2_382 | ~spl2_560)),
% 37.20/5.20    inference(superposition,[],[f10962,f19246])).
% 37.20/5.20  fof(f19246,plain,(
% 37.20/5.20    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_560),
% 37.20/5.20    inference(avatar_component_clause,[],[f19244])).
% 37.20/5.20  fof(f10962,plain,(
% 37.20/5.20    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X2,X0)),X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl2_382),
% 37.20/5.20    inference(avatar_component_clause,[],[f10961])).
% 37.20/5.20  fof(f19583,plain,(
% 37.20/5.20    spl2_576 | ~spl2_384 | ~spl2_560),
% 37.20/5.20    inference(avatar_split_clause,[],[f19284,f19244,f10969,f19580])).
% 37.20/5.20  fof(f10969,plain,(
% 37.20/5.20    spl2_384 <=> ! [X1,X0] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_384])])).
% 37.20/5.20  fof(f19284,plain,(
% 37.20/5.20    r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1)) | (~spl2_384 | ~spl2_560)),
% 37.20/5.20    inference(superposition,[],[f10970,f19246])).
% 37.20/5.20  fof(f10970,plain,(
% 37.20/5.20    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))) ) | ~spl2_384),
% 37.20/5.20    inference(avatar_component_clause,[],[f10969])).
% 37.20/5.20  fof(f19540,plain,(
% 37.20/5.20    spl2_573 | ~spl2_376 | ~spl2_560),
% 37.20/5.20    inference(avatar_split_clause,[],[f19281,f19244,f10920,f19537])).
% 37.20/5.20  fof(f10920,plain,(
% 37.20/5.20    spl2_376 <=> ! [X1,X2] : k4_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0,X1) = X1),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_376])])).
% 37.20/5.20  fof(f19281,plain,(
% 37.20/5.20    sK1 = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,sK1) | (~spl2_376 | ~spl2_560)),
% 37.20/5.20    inference(superposition,[],[f10921,f19246])).
% 37.20/5.20  fof(f10921,plain,(
% 37.20/5.20    ( ! [X2,X1] : (k4_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0,X1) = X1) ) | ~spl2_376),
% 37.20/5.20    inference(avatar_component_clause,[],[f10920])).
% 37.20/5.20  fof(f19518,plain,(
% 37.20/5.20    spl2_572 | ~spl2_325 | ~spl2_560),
% 37.20/5.20    inference(avatar_split_clause,[],[f19279,f19244,f5630,f19515])).
% 37.20/5.20  fof(f5630,plain,(
% 37.20/5.20    spl2_325 <=> ! [X3,X2] : k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3)))) = X2),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_325])])).
% 37.20/5.20  fof(f19279,plain,(
% 37.20/5.20    sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | (~spl2_325 | ~spl2_560)),
% 37.20/5.20    inference(superposition,[],[f5631,f19246])).
% 37.20/5.20  fof(f5631,plain,(
% 37.20/5.20    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3)))) = X2) ) | ~spl2_325),
% 37.20/5.20    inference(avatar_component_clause,[],[f5630])).
% 37.20/5.20  fof(f19307,plain,(
% 37.20/5.20    spl2_562 | ~spl2_131 | ~spl2_560),
% 37.20/5.20    inference(avatar_split_clause,[],[f19261,f19244,f1558,f19304])).
% 37.20/5.20  fof(f1558,plain,(
% 37.20/5.20    spl2_131 <=> ! [X1,X0] : r1_tarski(X1,k3_tarski(k2_tarski(X1,X0)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).
% 37.20/5.20  fof(f19261,plain,(
% 37.20/5.20    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_131 | ~spl2_560)),
% 37.20/5.20    inference(superposition,[],[f1559,f19246])).
% 37.20/5.20  fof(f1559,plain,(
% 37.20/5.20    ( ! [X0,X1] : (r1_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) ) | ~spl2_131),
% 37.20/5.20    inference(avatar_component_clause,[],[f1558])).
% 37.20/5.20  fof(f19247,plain,(
% 37.20/5.20    spl2_560 | ~spl2_4 | ~spl2_103 | ~spl2_485 | ~spl2_509),
% 37.20/5.20    inference(avatar_split_clause,[],[f18494,f17462,f16572,f1171,f122,f19244])).
% 37.20/5.20  fof(f1171,plain,(
% 37.20/5.20    spl2_103 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).
% 37.20/5.20  fof(f16572,plain,(
% 37.20/5.20    spl2_485 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k3_tarski(k2_tarski(sK1,X2)) = k4_subset_1(u1_struct_0(sK0),sK1,X2))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_485])])).
% 37.20/5.20  fof(f17462,plain,(
% 37.20/5.20    spl2_509 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_509])])).
% 37.20/5.20  fof(f18494,plain,(
% 37.20/5.20    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_103 | ~spl2_485 | ~spl2_509)),
% 37.20/5.20    inference(backward_demodulation,[],[f16878,f18037])).
% 37.20/5.20  fof(f18037,plain,(
% 37.20/5.20    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_509)),
% 37.20/5.20    inference(resolution,[],[f17463,f124])).
% 37.20/5.20  fof(f17463,plain,(
% 37.20/5.20    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_509),
% 37.20/5.20    inference(avatar_component_clause,[],[f17462])).
% 37.20/5.20  fof(f16878,plain,(
% 37.20/5.20    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_103 | ~spl2_485)),
% 37.20/5.20    inference(resolution,[],[f16573,f1173])).
% 37.20/5.20  fof(f1173,plain,(
% 37.20/5.20    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_103),
% 37.20/5.20    inference(avatar_component_clause,[],[f1171])).
% 37.20/5.20  fof(f16573,plain,(
% 37.20/5.20    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k3_tarski(k2_tarski(sK1,X2)) = k4_subset_1(u1_struct_0(sK0),sK1,X2)) ) | ~spl2_485),
% 37.20/5.20    inference(avatar_component_clause,[],[f16572])).
% 37.20/5.20  fof(f18709,plain,(
% 37.20/5.20    ~spl2_7 | ~spl2_34 | ~spl2_175 | ~spl2_289 | ~spl2_326 | ~spl2_390 | ~spl2_402 | ~spl2_524 | ~spl2_533),
% 37.20/5.20    inference(avatar_contradiction_clause,[],[f18708])).
% 37.20/5.20  fof(f18708,plain,(
% 37.20/5.20    $false | (~spl2_7 | ~spl2_34 | ~spl2_175 | ~spl2_289 | ~spl2_326 | ~spl2_390 | ~spl2_402 | ~spl2_524 | ~spl2_533)),
% 37.20/5.20    inference(subsumption_resolution,[],[f18707,f18658])).
% 37.20/5.20  fof(f18658,plain,(
% 37.20/5.20    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_34 | ~spl2_175 | ~spl2_289 | ~spl2_390 | ~spl2_402 | ~spl2_524)),
% 37.20/5.20    inference(subsumption_resolution,[],[f18493,f326])).
% 37.20/5.20  fof(f326,plain,(
% 37.20/5.20    v4_pre_topc(sK1,sK0) | ~spl2_34),
% 37.20/5.20    inference(avatar_component_clause,[],[f324])).
% 37.20/5.20  fof(f18493,plain,(
% 37.20/5.20    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | (~spl2_175 | ~spl2_289 | ~spl2_390 | ~spl2_402 | ~spl2_524)),
% 37.20/5.20    inference(forward_demodulation,[],[f2791,f17976])).
% 37.20/5.20  fof(f17976,plain,(
% 37.20/5.20    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_289 | ~spl2_390 | ~spl2_402 | ~spl2_524)),
% 37.20/5.20    inference(backward_demodulation,[],[f17975,f17969])).
% 37.20/5.20  fof(f17969,plain,(
% 37.20/5.20    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_402 | ~spl2_524)),
% 37.20/5.20    inference(superposition,[],[f11642,f17948])).
% 37.20/5.20  fof(f17948,plain,(
% 37.20/5.20    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_524),
% 37.20/5.20    inference(avatar_component_clause,[],[f17946])).
% 37.20/5.20  fof(f17946,plain,(
% 37.20/5.20    spl2_524 <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_524])])).
% 37.20/5.20  fof(f11642,plain,(
% 37.20/5.20    ( ! [X50,X49] : (k3_subset_1(X49,k7_subset_1(X49,X49,X50)) = k1_setfam_1(k2_tarski(X49,X50))) ) | ~spl2_402),
% 37.20/5.20    inference(avatar_component_clause,[],[f11641])).
% 37.20/5.20  fof(f11641,plain,(
% 37.20/5.20    spl2_402 <=> ! [X49,X50] : k3_subset_1(X49,k7_subset_1(X49,X49,X50)) = k1_setfam_1(k2_tarski(X49,X50))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_402])])).
% 37.20/5.20  fof(f17975,plain,(
% 37.20/5.20    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_289 | ~spl2_390 | ~spl2_524)),
% 37.20/5.20    inference(forward_demodulation,[],[f17967,f11269])).
% 37.20/5.20  fof(f11269,plain,(
% 37.20/5.20    ( ! [X4,X3] : (k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) = k7_subset_1(X3,X3,X4)) ) | ~spl2_390),
% 37.20/5.20    inference(avatar_component_clause,[],[f11268])).
% 37.20/5.20  fof(f11268,plain,(
% 37.20/5.20    spl2_390 <=> ! [X3,X4] : k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) = k7_subset_1(X3,X3,X4)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_390])])).
% 37.20/5.20  fof(f17967,plain,(
% 37.20/5.20    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) | (~spl2_289 | ~spl2_524)),
% 37.20/5.20    inference(superposition,[],[f4951,f17948])).
% 37.20/5.20  fof(f4951,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))))) ) | ~spl2_289),
% 37.20/5.20    inference(avatar_component_clause,[],[f4950])).
% 37.20/5.20  fof(f4950,plain,(
% 37.20/5.20    spl2_289 <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_289])])).
% 37.20/5.20  fof(f2791,plain,(
% 37.20/5.20    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_175),
% 37.20/5.20    inference(forward_demodulation,[],[f63,f2782])).
% 37.20/5.20  fof(f2782,plain,(
% 37.20/5.20    ( ! [X21] : (k7_subset_1(u1_struct_0(sK0),sK1,X21) = k7_subset_1(sK1,sK1,X21)) ) | ~spl2_175),
% 37.20/5.20    inference(avatar_component_clause,[],[f2781])).
% 37.20/5.20  fof(f2781,plain,(
% 37.20/5.20    spl2_175 <=> ! [X21] : k7_subset_1(u1_struct_0(sK0),sK1,X21) = k7_subset_1(sK1,sK1,X21)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_175])])).
% 37.20/5.20  fof(f63,plain,(
% 37.20/5.20    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 37.20/5.20    inference(cnf_transformation,[],[f57])).
% 37.20/5.20  fof(f57,plain,(
% 37.20/5.20    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 37.20/5.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).
% 37.20/5.20  fof(f55,plain,(
% 37.20/5.20    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 37.20/5.20    introduced(choice_axiom,[])).
% 37.20/5.20  fof(f56,plain,(
% 37.20/5.20    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 37.20/5.20    introduced(choice_axiom,[])).
% 37.20/5.20  fof(f54,plain,(
% 37.20/5.20    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 37.20/5.20    inference(flattening,[],[f53])).
% 37.20/5.20  fof(f53,plain,(
% 37.20/5.20    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 37.20/5.20    inference(nnf_transformation,[],[f31])).
% 37.20/5.20  fof(f31,plain,(
% 37.20/5.20    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 37.20/5.20    inference(flattening,[],[f30])).
% 37.20/5.20  fof(f30,plain,(
% 37.20/5.20    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 37.20/5.20    inference(ennf_transformation,[],[f29])).
% 37.20/5.20  fof(f29,negated_conjecture,(
% 37.20/5.20    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 37.20/5.20    inference(negated_conjecture,[],[f28])).
% 37.20/5.20  fof(f28,conjecture,(
% 37.20/5.20    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 37.20/5.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 37.20/5.20  fof(f18707,plain,(
% 37.20/5.20    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_7 | ~spl2_326 | ~spl2_402 | ~spl2_524 | ~spl2_533)),
% 37.20/5.20    inference(backward_demodulation,[],[f17969,f18706])).
% 37.20/5.20  fof(f18706,plain,(
% 37.20/5.20    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_7 | ~spl2_326 | ~spl2_533)),
% 37.20/5.20    inference(forward_demodulation,[],[f18689,f136])).
% 37.20/5.20  fof(f136,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_7),
% 37.20/5.20    inference(avatar_component_clause,[],[f135])).
% 37.20/5.20  fof(f135,plain,(
% 37.20/5.20    spl2_7 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 37.20/5.20  fof(f18689,plain,(
% 37.20/5.20    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | (~spl2_326 | ~spl2_533)),
% 37.20/5.20    inference(superposition,[],[f5635,f18491])).
% 37.20/5.20  fof(f18491,plain,(
% 37.20/5.20    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_533),
% 37.20/5.20    inference(avatar_component_clause,[],[f18489])).
% 37.20/5.20  fof(f18489,plain,(
% 37.20/5.20    spl2_533 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_533])])).
% 37.20/5.20  fof(f5635,plain,(
% 37.20/5.20    ( ! [X4,X5] : (k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4)))) = X4) ) | ~spl2_326),
% 37.20/5.20    inference(avatar_component_clause,[],[f5634])).
% 37.20/5.20  fof(f5634,plain,(
% 37.20/5.20    spl2_326 <=> ! [X5,X4] : k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4)))) = X4),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_326])])).
% 37.20/5.20  fof(f18492,plain,(
% 37.20/5.20    spl2_533 | ~spl2_4 | ~spl2_103 | ~spl2_286 | ~spl2_485 | ~spl2_509),
% 37.20/5.20    inference(avatar_split_clause,[],[f18427,f17462,f16572,f4907,f1171,f122,f18489])).
% 37.20/5.20  fof(f18427,plain,(
% 37.20/5.20    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_103 | ~spl2_286 | ~spl2_485 | ~spl2_509)),
% 37.20/5.20    inference(backward_demodulation,[],[f16878,f18426])).
% 37.20/5.20  fof(f18426,plain,(
% 37.20/5.20    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_286 | ~spl2_509)),
% 37.20/5.20    inference(forward_demodulation,[],[f18037,f4909])).
% 37.20/5.20  fof(f17949,plain,(
% 37.20/5.20    spl2_524 | ~spl2_175 | ~spl2_523),
% 37.20/5.20    inference(avatar_split_clause,[],[f17943,f17939,f2781,f17946])).
% 37.20/5.20  fof(f17939,plain,(
% 37.20/5.20    spl2_523 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_523])])).
% 37.20/5.20  fof(f17943,plain,(
% 37.20/5.20    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_175 | ~spl2_523)),
% 37.20/5.20    inference(superposition,[],[f17941,f2782])).
% 37.20/5.20  fof(f17941,plain,(
% 37.20/5.20    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_523),
% 37.20/5.20    inference(avatar_component_clause,[],[f17939])).
% 37.20/5.20  fof(f17942,plain,(
% 37.20/5.20    spl2_523 | ~spl2_4 | ~spl2_501),
% 37.20/5.20    inference(avatar_split_clause,[],[f17791,f17181,f122,f17939])).
% 37.20/5.20  fof(f17181,plain,(
% 37.20/5.20    spl2_501 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_501])])).
% 37.20/5.20  fof(f17791,plain,(
% 37.20/5.20    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_501)),
% 37.20/5.20    inference(resolution,[],[f17182,f124])).
% 37.20/5.20  fof(f17182,plain,(
% 37.20/5.20    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_501),
% 37.20/5.20    inference(avatar_component_clause,[],[f17181])).
% 37.20/5.20  fof(f17464,plain,(
% 37.20/5.20    spl2_509 | ~spl2_2 | ~spl2_395),
% 37.20/5.20    inference(avatar_split_clause,[],[f11993,f11288,f113,f17462])).
% 37.20/5.20  fof(f11288,plain,(
% 37.20/5.20    spl2_395 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_395])])).
% 37.20/5.20  fof(f11993,plain,(
% 37.20/5.20    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_395)),
% 37.20/5.20    inference(resolution,[],[f11289,f115])).
% 37.20/5.20  fof(f11289,plain,(
% 37.20/5.20    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) ) | ~spl2_395),
% 37.20/5.20    inference(avatar_component_clause,[],[f11288])).
% 37.20/5.20  fof(f17183,plain,(
% 37.20/5.20    spl2_501 | ~spl2_2 | ~spl2_383),
% 37.20/5.20    inference(avatar_split_clause,[],[f11735,f10965,f113,f17181])).
% 37.20/5.20  fof(f10965,plain,(
% 37.20/5.20    spl2_383 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_383])])).
% 37.20/5.20  fof(f11735,plain,(
% 37.20/5.20    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_383)),
% 37.20/5.20    inference(resolution,[],[f10966,f115])).
% 37.20/5.20  fof(f10966,plain,(
% 37.20/5.20    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) ) | ~spl2_383),
% 37.20/5.20    inference(avatar_component_clause,[],[f10965])).
% 37.20/5.20  fof(f16574,plain,(
% 37.20/5.20    spl2_485 | ~spl2_4 | ~spl2_336),
% 37.20/5.20    inference(avatar_split_clause,[],[f15132,f5736,f122,f16572])).
% 37.20/5.20  fof(f5736,plain,(
% 37.20/5.20    spl2_336 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_336])])).
% 37.20/5.20  fof(f15132,plain,(
% 37.20/5.20    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k3_tarski(k2_tarski(sK1,X2)) = k4_subset_1(u1_struct_0(sK0),sK1,X2)) ) | (~spl2_4 | ~spl2_336)),
% 37.20/5.20    inference(resolution,[],[f124,f5737])).
% 37.20/5.20  fof(f5737,plain,(
% 37.20/5.20    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) ) | ~spl2_336),
% 37.20/5.20    inference(avatar_component_clause,[],[f5736])).
% 37.20/5.20  fof(f15618,plain,(
% 37.20/5.20    spl2_463 | ~spl2_173 | ~spl2_176),
% 37.20/5.20    inference(avatar_split_clause,[],[f15593,f2787,f2754,f15615])).
% 37.20/5.20  fof(f2754,plain,(
% 37.20/5.20    spl2_173 <=> ! [X1,X0] : r1_tarski(k7_subset_1(X0,X0,X1),X0)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_173])])).
% 37.20/5.20  fof(f2787,plain,(
% 37.20/5.20    spl2_176 <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).
% 37.20/5.20  fof(f15593,plain,(
% 37.20/5.20    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_173 | ~spl2_176)),
% 37.20/5.20    inference(superposition,[],[f2755,f2789])).
% 37.20/5.20  fof(f2789,plain,(
% 37.20/5.20    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~spl2_176),
% 37.20/5.20    inference(avatar_component_clause,[],[f2787])).
% 37.20/5.20  fof(f2755,plain,(
% 37.20/5.20    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) ) | ~spl2_173),
% 37.20/5.20    inference(avatar_component_clause,[],[f2754])).
% 37.20/5.20  fof(f11988,plain,(
% 37.20/5.20    spl2_413 | ~spl2_7 | ~spl2_390),
% 37.20/5.20    inference(avatar_split_clause,[],[f11291,f11268,f135,f11986])).
% 37.20/5.20  fof(f11291,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)) ) | (~spl2_7 | ~spl2_390)),
% 37.20/5.20    inference(superposition,[],[f11269,f136])).
% 37.20/5.20  fof(f11643,plain,(
% 37.20/5.20    spl2_402 | ~spl2_173 | ~spl2_289 | ~spl2_368 | ~spl2_390),
% 37.20/5.20    inference(avatar_split_clause,[],[f11441,f11268,f10516,f4950,f2754,f11641])).
% 37.20/5.20  fof(f11441,plain,(
% 37.20/5.20    ( ! [X50,X49] : (k3_subset_1(X49,k7_subset_1(X49,X49,X50)) = k1_setfam_1(k2_tarski(X49,X50))) ) | (~spl2_173 | ~spl2_289 | ~spl2_368 | ~spl2_390)),
% 37.20/5.20    inference(backward_demodulation,[],[f10544,f11298])).
% 37.20/5.20  fof(f11298,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1))) ) | (~spl2_289 | ~spl2_390)),
% 37.20/5.20    inference(superposition,[],[f11269,f4951])).
% 37.20/5.20  fof(f10544,plain,(
% 37.20/5.20    ( ! [X50,X49] : (k3_subset_1(X49,k7_subset_1(X49,X49,X50)) = k7_subset_1(X49,X49,k7_subset_1(X49,X49,X50))) ) | (~spl2_173 | ~spl2_368)),
% 37.20/5.20    inference(resolution,[],[f10517,f2755])).
% 37.20/5.20  fof(f11290,plain,(
% 37.20/5.20    spl2_395),
% 37.20/5.20    inference(avatar_split_clause,[],[f69,f11288])).
% 37.20/5.20  fof(f69,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 37.20/5.20    inference(cnf_transformation,[],[f34])).
% 37.20/5.20  fof(f34,plain,(
% 37.20/5.20    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 37.20/5.20    inference(ennf_transformation,[],[f26])).
% 37.20/5.20  fof(f26,axiom,(
% 37.20/5.20    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 37.20/5.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 37.20/5.20  fof(f11270,plain,(
% 37.20/5.20    spl2_390 | ~spl2_56 | ~spl2_151),
% 37.20/5.20    inference(avatar_split_clause,[],[f2609,f2292,f497,f11268])).
% 37.20/5.20  fof(f497,plain,(
% 37.20/5.20    spl2_56 <=> ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 37.20/5.20  fof(f2292,plain,(
% 37.20/5.20    spl2_151 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).
% 37.20/5.20  fof(f2609,plain,(
% 37.20/5.20    ( ! [X4,X3] : (k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) = k7_subset_1(X3,X3,X4)) ) | (~spl2_56 | ~spl2_151)),
% 37.20/5.20    inference(resolution,[],[f2293,f498])).
% 37.20/5.20  fof(f498,plain,(
% 37.20/5.20    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1))) ) | ~spl2_56),
% 37.20/5.20    inference(avatar_component_clause,[],[f497])).
% 37.20/5.20  fof(f2293,plain,(
% 37.20/5.20    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ) | ~spl2_151),
% 37.20/5.20    inference(avatar_component_clause,[],[f2292])).
% 37.20/5.20  fof(f10971,plain,(
% 37.20/5.20    spl2_384 | ~spl2_41 | ~spl2_311),
% 37.20/5.20    inference(avatar_split_clause,[],[f5400,f5374,f386,f10969])).
% 37.20/5.20  fof(f386,plain,(
% 37.20/5.20    spl2_41 <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 37.20/5.20  fof(f5374,plain,(
% 37.20/5.20    spl2_311 <=> ! [X1,X0] : r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_311])])).
% 37.20/5.20  fof(f5400,plain,(
% 37.20/5.20    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))) ) | (~spl2_41 | ~spl2_311)),
% 37.20/5.20    inference(superposition,[],[f5375,f387])).
% 37.20/5.20  fof(f387,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) ) | ~spl2_41),
% 37.20/5.20    inference(avatar_component_clause,[],[f386])).
% 37.20/5.20  fof(f5375,plain,(
% 37.20/5.20    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)) ) | ~spl2_311),
% 37.20/5.20    inference(avatar_component_clause,[],[f5374])).
% 37.20/5.20  fof(f10967,plain,(
% 37.20/5.20    spl2_383),
% 37.20/5.20    inference(avatar_split_clause,[],[f68,f10965])).
% 37.20/5.20  fof(f68,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 37.20/5.20    inference(cnf_transformation,[],[f33])).
% 37.20/5.20  fof(f33,plain,(
% 37.20/5.20    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 37.20/5.20    inference(ennf_transformation,[],[f27])).
% 37.20/5.20  fof(f27,axiom,(
% 37.20/5.20    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 37.20/5.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 37.20/5.20  fof(f10963,plain,(
% 37.20/5.20    spl2_382 | ~spl2_15 | ~spl2_311),
% 37.20/5.20    inference(avatar_split_clause,[],[f5377,f5374,f186,f10961])).
% 37.20/5.20  fof(f186,plain,(
% 37.20/5.20    spl2_15 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 37.20/5.20  fof(f5377,plain,(
% 37.20/5.20    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X2,X0)),X2),X1)) ) | (~spl2_15 | ~spl2_311)),
% 37.20/5.20    inference(resolution,[],[f5375,f187])).
% 37.20/5.20  fof(f187,plain,(
% 37.20/5.20    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl2_15),
% 37.20/5.20    inference(avatar_component_clause,[],[f186])).
% 37.20/5.20  fof(f10922,plain,(
% 37.20/5.20    spl2_376 | ~spl2_131 | ~spl2_375),
% 37.20/5.20    inference(avatar_split_clause,[],[f10877,f10873,f1558,f10920])).
% 37.20/5.20  fof(f10873,plain,(
% 37.20/5.20    spl2_375 <=> ! [X1,X0] : (k4_subset_1(X0,k1_xboole_0,X1) = X1 | ~r1_tarski(X1,X0))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_375])])).
% 37.20/5.20  fof(f10877,plain,(
% 37.20/5.20    ( ! [X2,X1] : (k4_subset_1(k3_tarski(k2_tarski(X1,X2)),k1_xboole_0,X1) = X1) ) | (~spl2_131 | ~spl2_375)),
% 37.20/5.20    inference(resolution,[],[f10874,f1559])).
% 37.20/5.20  fof(f10874,plain,(
% 37.20/5.20    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_subset_1(X0,k1_xboole_0,X1) = X1) ) | ~spl2_375),
% 37.20/5.20    inference(avatar_component_clause,[],[f10873])).
% 37.20/5.20  fof(f10875,plain,(
% 37.20/5.20    spl2_375 | ~spl2_9 | ~spl2_372),
% 37.20/5.20    inference(avatar_split_clause,[],[f10853,f10850,f143,f10873])).
% 37.20/5.20  fof(f143,plain,(
% 37.20/5.20    spl2_9 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 37.20/5.20  fof(f10850,plain,(
% 37.20/5.20    spl2_372 <=> ! [X7,X6] : (k4_subset_1(X7,k1_xboole_0,X6) = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X7)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_372])])).
% 37.20/5.20  fof(f10853,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k4_subset_1(X0,k1_xboole_0,X1) = X1 | ~r1_tarski(X1,X0)) ) | (~spl2_9 | ~spl2_372)),
% 37.20/5.20    inference(resolution,[],[f10851,f144])).
% 37.20/5.20  fof(f144,plain,(
% 37.20/5.20    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_9),
% 37.20/5.20    inference(avatar_component_clause,[],[f143])).
% 37.20/5.20  fof(f10851,plain,(
% 37.20/5.20    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(X7)) | k4_subset_1(X7,k1_xboole_0,X6) = X6) ) | ~spl2_372),
% 37.20/5.20    inference(avatar_component_clause,[],[f10850])).
% 37.20/5.20  fof(f10852,plain,(
% 37.20/5.20    spl2_372 | ~spl2_137 | ~spl2_336 | ~spl2_369),
% 37.20/5.20    inference(avatar_split_clause,[],[f10764,f10708,f5736,f2129,f10850])).
% 37.20/5.20  fof(f2129,plain,(
% 37.20/5.20    spl2_137 <=> ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).
% 37.20/5.20  fof(f10708,plain,(
% 37.20/5.20    spl2_369 <=> ! [X4] : k3_tarski(k2_tarski(k1_xboole_0,X4)) = X4),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_369])])).
% 37.20/5.20  fof(f10764,plain,(
% 37.20/5.20    ( ! [X6,X7] : (k4_subset_1(X7,k1_xboole_0,X6) = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X7))) ) | (~spl2_137 | ~spl2_336 | ~spl2_369)),
% 37.20/5.20    inference(forward_demodulation,[],[f10756,f10709])).
% 37.20/5.20  fof(f10709,plain,(
% 37.20/5.20    ( ! [X4] : (k3_tarski(k2_tarski(k1_xboole_0,X4)) = X4) ) | ~spl2_369),
% 37.20/5.20    inference(avatar_component_clause,[],[f10708])).
% 37.20/5.20  fof(f10756,plain,(
% 37.20/5.20    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(X7)) | k3_tarski(k2_tarski(k1_xboole_0,X6)) = k4_subset_1(X7,k1_xboole_0,X6)) ) | (~spl2_137 | ~spl2_336)),
% 37.20/5.20    inference(resolution,[],[f5737,f2130])).
% 37.20/5.20  fof(f2130,plain,(
% 37.20/5.20    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) ) | ~spl2_137),
% 37.20/5.20    inference(avatar_component_clause,[],[f2129])).
% 37.20/5.20  fof(f10710,plain,(
% 37.20/5.20    spl2_369 | ~spl2_22 | ~spl2_135 | ~spl2_203 | ~spl2_247 | ~spl2_368),
% 37.20/5.20    inference(avatar_split_clause,[],[f10574,f10516,f4043,f3348,f2116,f227,f10708])).
% 37.20/5.20  fof(f2116,plain,(
% 37.20/5.20    spl2_135 <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).
% 37.20/5.20  fof(f3348,plain,(
% 37.20/5.20    spl2_203 <=> ! [X3,X4] : k1_xboole_0 = k7_subset_1(X3,X3,k3_tarski(k2_tarski(X4,X3)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).
% 37.20/5.20  fof(f4043,plain,(
% 37.20/5.20    spl2_247 <=> ! [X10] : r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X10)),X10)),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_247])])).
% 37.20/5.20  fof(f10574,plain,(
% 37.20/5.20    ( ! [X4] : (k3_tarski(k2_tarski(k1_xboole_0,X4)) = X4) ) | (~spl2_22 | ~spl2_135 | ~spl2_203 | ~spl2_247 | ~spl2_368)),
% 37.20/5.20    inference(forward_demodulation,[],[f10573,f2117])).
% 37.20/5.20  fof(f2117,plain,(
% 37.20/5.20    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | ~spl2_135),
% 37.20/5.20    inference(avatar_component_clause,[],[f2116])).
% 37.20/5.20  fof(f10573,plain,(
% 37.20/5.20    ( ! [X4] : (k3_subset_1(X4,k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X4))) ) | (~spl2_22 | ~spl2_203 | ~spl2_247 | ~spl2_368)),
% 37.20/5.20    inference(backward_demodulation,[],[f4051,f10570])).
% 37.20/5.20  fof(f10570,plain,(
% 37.20/5.20    ( ! [X36] : (k1_xboole_0 = k3_subset_1(X36,k3_tarski(k2_tarski(k1_xboole_0,X36)))) ) | (~spl2_203 | ~spl2_247 | ~spl2_368)),
% 37.20/5.20    inference(forward_demodulation,[],[f10535,f3349])).
% 37.20/5.20  fof(f3349,plain,(
% 37.20/5.20    ( ! [X4,X3] : (k1_xboole_0 = k7_subset_1(X3,X3,k3_tarski(k2_tarski(X4,X3)))) ) | ~spl2_203),
% 37.20/5.20    inference(avatar_component_clause,[],[f3348])).
% 37.20/5.20  fof(f10535,plain,(
% 37.20/5.20    ( ! [X36] : (k3_subset_1(X36,k3_tarski(k2_tarski(k1_xboole_0,X36))) = k7_subset_1(X36,X36,k3_tarski(k2_tarski(k1_xboole_0,X36)))) ) | (~spl2_247 | ~spl2_368)),
% 37.20/5.20    inference(resolution,[],[f10517,f4044])).
% 37.20/5.20  fof(f4044,plain,(
% 37.20/5.20    ( ! [X10] : (r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X10)),X10)) ) | ~spl2_247),
% 37.20/5.20    inference(avatar_component_clause,[],[f4043])).
% 37.20/5.20  fof(f4051,plain,(
% 37.20/5.20    ( ! [X4] : (k3_tarski(k2_tarski(k1_xboole_0,X4)) = k3_subset_1(X4,k3_subset_1(X4,k3_tarski(k2_tarski(k1_xboole_0,X4))))) ) | (~spl2_22 | ~spl2_247)),
% 37.20/5.20    inference(resolution,[],[f4044,f228])).
% 37.20/5.20  fof(f10518,plain,(
% 37.20/5.20    spl2_368 | ~spl2_9 | ~spl2_56 | ~spl2_66 | ~spl2_151),
% 37.20/5.20    inference(avatar_split_clause,[],[f2649,f2292,f600,f497,f143,f10516])).
% 37.20/5.20  fof(f600,plain,(
% 37.20/5.20    spl2_66 <=> ! [X1,X0] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 37.20/5.20  fof(f2649,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) | ~r1_tarski(X1,X0)) ) | (~spl2_9 | ~spl2_56 | ~spl2_66 | ~spl2_151)),
% 37.20/5.20    inference(backward_demodulation,[],[f1227,f2609])).
% 37.20/5.20  fof(f1227,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X1,X0)) ) | (~spl2_9 | ~spl2_66)),
% 37.20/5.20    inference(resolution,[],[f601,f144])).
% 37.20/5.20  fof(f601,plain,(
% 37.20/5.20    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl2_66),
% 37.20/5.20    inference(avatar_component_clause,[],[f600])).
% 37.20/5.20  fof(f5738,plain,(
% 37.20/5.20    spl2_336),
% 37.20/5.20    inference(avatar_split_clause,[],[f104,f5736])).
% 37.20/5.20  fof(f104,plain,(
% 37.20/5.20    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.20    inference(definition_unfolding,[],[f92,f75])).
% 37.20/5.20  fof(f75,plain,(
% 37.20/5.20    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 37.20/5.20    inference(cnf_transformation,[],[f12])).
% 37.20/5.20  fof(f12,axiom,(
% 37.20/5.20    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 37.20/5.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 37.20/5.20  fof(f92,plain,(
% 37.20/5.20    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.20    inference(cnf_transformation,[],[f52])).
% 37.20/5.20  fof(f52,plain,(
% 37.20/5.20    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.20    inference(flattening,[],[f51])).
% 37.20/5.20  fof(f51,plain,(
% 37.20/5.20    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 37.20/5.20    inference(ennf_transformation,[],[f17])).
% 37.20/5.20  fof(f17,axiom,(
% 37.20/5.20    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 37.20/5.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 37.20/5.20  fof(f5636,plain,(
% 37.20/5.20    spl2_326 | ~spl2_56 | ~spl2_151 | ~spl2_203 | ~spl2_234 | ~spl2_289),
% 37.20/5.20    inference(avatar_split_clause,[],[f5128,f4950,f3814,f3348,f2292,f497,f5634])).
% 37.20/5.20  fof(f3814,plain,(
% 37.20/5.20    spl2_234 <=> ! [X3] : k7_subset_1(X3,X3,k1_xboole_0) = X3),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_234])])).
% 37.20/5.20  fof(f5128,plain,(
% 37.20/5.20    ( ! [X4,X5] : (k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4)))) = X4) ) | (~spl2_56 | ~spl2_151 | ~spl2_203 | ~spl2_234 | ~spl2_289)),
% 37.20/5.20    inference(forward_demodulation,[],[f5127,f3815])).
% 37.20/5.20  fof(f3815,plain,(
% 37.20/5.20    ( ! [X3] : (k7_subset_1(X3,X3,k1_xboole_0) = X3) ) | ~spl2_234),
% 37.20/5.20    inference(avatar_component_clause,[],[f3814])).
% 37.20/5.20  fof(f5127,plain,(
% 37.20/5.20    ( ! [X4,X5] : (k7_subset_1(X4,X4,k1_xboole_0) = k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4))))) ) | (~spl2_56 | ~spl2_151 | ~spl2_203 | ~spl2_289)),
% 37.20/5.20    inference(forward_demodulation,[],[f5111,f2609])).
% 37.20/5.20  fof(f5111,plain,(
% 37.20/5.20    ( ! [X4,X5] : (k1_setfam_1(k2_tarski(X4,k3_tarski(k2_tarski(X5,X4)))) = k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,k1_xboole_0)))) ) | (~spl2_203 | ~spl2_289)),
% 37.20/5.20    inference(superposition,[],[f4951,f3349])).
% 37.20/5.20  fof(f5632,plain,(
% 37.20/5.20    spl2_325 | ~spl2_56 | ~spl2_151 | ~spl2_202 | ~spl2_234 | ~spl2_289),
% 37.20/5.20    inference(avatar_split_clause,[],[f5125,f4950,f3814,f3344,f2292,f497,f5630])).
% 37.20/5.20  fof(f3344,plain,(
% 37.20/5.20    spl2_202 <=> ! [X1,X2] : k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2)))),
% 37.20/5.20    introduced(avatar_definition,[new_symbols(naming,[spl2_202])])).
% 37.20/5.21  fof(f5125,plain,(
% 37.20/5.21    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3)))) = X2) ) | (~spl2_56 | ~spl2_151 | ~spl2_202 | ~spl2_234 | ~spl2_289)),
% 37.20/5.21    inference(forward_demodulation,[],[f5124,f3815])).
% 37.20/5.21  fof(f5124,plain,(
% 37.20/5.21    ( ! [X2,X3] : (k7_subset_1(X2,X2,k1_xboole_0) = k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3))))) ) | (~spl2_56 | ~spl2_151 | ~spl2_202 | ~spl2_289)),
% 37.20/5.21    inference(forward_demodulation,[],[f5110,f2609])).
% 37.20/5.21  fof(f5110,plain,(
% 37.20/5.21    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X2,k3_tarski(k2_tarski(X2,X3)))) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_xboole_0)))) ) | (~spl2_202 | ~spl2_289)),
% 37.20/5.21    inference(superposition,[],[f4951,f3345])).
% 37.20/5.21  fof(f3345,plain,(
% 37.20/5.21    ( ! [X2,X1] : (k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2)))) ) | ~spl2_202),
% 37.20/5.21    inference(avatar_component_clause,[],[f3344])).
% 37.20/5.21  fof(f5376,plain,(
% 37.20/5.21    spl2_311 | ~spl2_7 | ~spl2_13 | ~spl2_56 | ~spl2_77 | ~spl2_151 | ~spl2_202 | ~spl2_234 | ~spl2_289),
% 37.20/5.21    inference(avatar_split_clause,[],[f5126,f4950,f3814,f3344,f2292,f768,f497,f172,f135,f5374])).
% 37.20/5.21  fof(f172,plain,(
% 37.20/5.21    spl2_13 <=> ! [X0] : r1_tarski(X0,X0)),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 37.20/5.21  fof(f768,plain,(
% 37.20/5.21    spl2_77 <=> ! [X1,X0,X2] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 37.20/5.21  fof(f5126,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)) ) | (~spl2_7 | ~spl2_13 | ~spl2_56 | ~spl2_77 | ~spl2_151 | ~spl2_202 | ~spl2_234 | ~spl2_289)),
% 37.20/5.21    inference(backward_demodulation,[],[f1355,f5125])).
% 37.20/5.21  fof(f1355,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))),X1)) ) | (~spl2_7 | ~spl2_13 | ~spl2_77)),
% 37.20/5.21    inference(forward_demodulation,[],[f1339,f136])).
% 37.20/5.21  fof(f1339,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))),X1)) ) | (~spl2_13 | ~spl2_77)),
% 37.20/5.21    inference(resolution,[],[f769,f173])).
% 37.20/5.21  fof(f173,plain,(
% 37.20/5.21    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl2_13),
% 37.20/5.21    inference(avatar_component_clause,[],[f172])).
% 37.20/5.21  fof(f769,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)) ) | ~spl2_77),
% 37.20/5.21    inference(avatar_component_clause,[],[f768])).
% 37.20/5.21  fof(f4952,plain,(
% 37.20/5.21    spl2_289 | ~spl2_56 | ~spl2_151),
% 37.20/5.21    inference(avatar_split_clause,[],[f2623,f2292,f497,f4950])).
% 37.20/5.21  fof(f2623,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k7_subset_1(X0,X0,X1))))) ) | (~spl2_56 | ~spl2_151)),
% 37.20/5.21    inference(backward_demodulation,[],[f97,f2609])).
% 37.20/5.21  fof(f97,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 37.20/5.21    inference(definition_unfolding,[],[f76,f74,f93,f93])).
% 37.20/5.21  fof(f93,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 37.20/5.21    inference(definition_unfolding,[],[f78,f74])).
% 37.20/5.21  fof(f78,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f1])).
% 37.20/5.21  fof(f1,axiom,(
% 37.20/5.21    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 37.20/5.21  fof(f74,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f20])).
% 37.20/5.21  fof(f20,axiom,(
% 37.20/5.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 37.20/5.21  fof(f76,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f9])).
% 37.20/5.21  fof(f9,axiom,(
% 37.20/5.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 37.20/5.21  fof(f4910,plain,(
% 37.20/5.21    spl2_286 | ~spl2_4 | ~spl2_34 | ~spl2_285),
% 37.20/5.21    inference(avatar_split_clause,[],[f4905,f4898,f324,f122,f4907])).
% 37.20/5.21  fof(f4898,plain,(
% 37.20/5.21    spl2_285 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_285])])).
% 37.20/5.21  fof(f4905,plain,(
% 37.20/5.21    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_4 | ~spl2_34 | ~spl2_285)),
% 37.20/5.21    inference(subsumption_resolution,[],[f4902,f124])).
% 37.20/5.21  fof(f4902,plain,(
% 37.20/5.21    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_34 | ~spl2_285)),
% 37.20/5.21    inference(resolution,[],[f4899,f326])).
% 37.20/5.21  fof(f4899,plain,(
% 37.20/5.21    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_285),
% 37.20/5.21    inference(avatar_component_clause,[],[f4898])).
% 37.20/5.21  fof(f4900,plain,(
% 37.20/5.21    spl2_285 | ~spl2_2 | ~spl2_138),
% 37.20/5.21    inference(avatar_split_clause,[],[f2428,f2150,f113,f4898])).
% 37.20/5.21  fof(f2150,plain,(
% 37.20/5.21    spl2_138 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).
% 37.20/5.21  fof(f2428,plain,(
% 37.20/5.21    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl2_2 | ~spl2_138)),
% 37.20/5.21    inference(resolution,[],[f2151,f115])).
% 37.20/5.21  fof(f2151,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) ) | ~spl2_138),
% 37.20/5.21    inference(avatar_component_clause,[],[f2150])).
% 37.20/5.21  fof(f4045,plain,(
% 37.20/5.21    spl2_247 | ~spl2_13 | ~spl2_246),
% 37.20/5.21    inference(avatar_split_clause,[],[f4006,f3996,f172,f4043])).
% 37.20/5.21  fof(f3996,plain,(
% 37.20/5.21    spl2_246 <=> ! [X11,X10] : (r1_tarski(X10,X11) | ~r1_tarski(X10,k3_tarski(k2_tarski(k1_xboole_0,X11))))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_246])])).
% 37.20/5.21  fof(f4006,plain,(
% 37.20/5.21    ( ! [X10] : (r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X10)),X10)) ) | (~spl2_13 | ~spl2_246)),
% 37.20/5.21    inference(resolution,[],[f3997,f173])).
% 37.20/5.21  fof(f3997,plain,(
% 37.20/5.21    ( ! [X10,X11] : (~r1_tarski(X10,k3_tarski(k2_tarski(k1_xboole_0,X11))) | r1_tarski(X10,X11)) ) | ~spl2_246),
% 37.20/5.21    inference(avatar_component_clause,[],[f3996])).
% 37.20/5.21  fof(f3998,plain,(
% 37.20/5.21    spl2_246 | ~spl2_213 | ~spl2_234),
% 37.20/5.21    inference(avatar_split_clause,[],[f3988,f3814,f3482,f3996])).
% 37.20/5.21  fof(f3482,plain,(
% 37.20/5.21    spl2_213 <=> ! [X1,X0,X2] : (r1_tarski(k7_subset_1(X0,X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_213])])).
% 37.20/5.21  fof(f3988,plain,(
% 37.20/5.21    ( ! [X10,X11] : (r1_tarski(X10,X11) | ~r1_tarski(X10,k3_tarski(k2_tarski(k1_xboole_0,X11)))) ) | (~spl2_213 | ~spl2_234)),
% 37.20/5.21    inference(superposition,[],[f3483,f3815])).
% 37.20/5.21  fof(f3483,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) ) | ~spl2_213),
% 37.20/5.21    inference(avatar_component_clause,[],[f3482])).
% 37.20/5.21  fof(f3816,plain,(
% 37.20/5.21    spl2_234 | ~spl2_135 | ~spl2_137 | ~spl2_201),
% 37.20/5.21    inference(avatar_split_clause,[],[f3812,f3340,f2129,f2116,f3814])).
% 37.20/5.21  fof(f3340,plain,(
% 37.20/5.21    spl2_201 <=> ! [X1,X0] : (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_201])])).
% 37.20/5.21  fof(f3812,plain,(
% 37.20/5.21    ( ! [X3] : (k7_subset_1(X3,X3,k1_xboole_0) = X3) ) | (~spl2_135 | ~spl2_137 | ~spl2_201)),
% 37.20/5.21    inference(forward_demodulation,[],[f3797,f2117])).
% 37.20/5.21  fof(f3797,plain,(
% 37.20/5.21    ( ! [X3] : (k3_subset_1(X3,k1_xboole_0) = k7_subset_1(X3,X3,k1_xboole_0)) ) | (~spl2_137 | ~spl2_201)),
% 37.20/5.21    inference(resolution,[],[f3341,f2130])).
% 37.20/5.21  fof(f3341,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) ) | ~spl2_201),
% 37.20/5.21    inference(avatar_component_clause,[],[f3340])).
% 37.20/5.21  fof(f3484,plain,(
% 37.20/5.21    spl2_213 | ~spl2_56 | ~spl2_77 | ~spl2_151),
% 37.20/5.21    inference(avatar_split_clause,[],[f2632,f2292,f768,f497,f3482])).
% 37.20/5.21  fof(f2632,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) ) | (~spl2_56 | ~spl2_77 | ~spl2_151)),
% 37.20/5.21    inference(backward_demodulation,[],[f769,f2609])).
% 37.20/5.21  fof(f3350,plain,(
% 37.20/5.21    spl2_203 | ~spl2_130 | ~spl2_197),
% 37.20/5.21    inference(avatar_split_clause,[],[f3237,f3168,f1523,f3348])).
% 37.20/5.21  fof(f1523,plain,(
% 37.20/5.21    spl2_130 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).
% 37.20/5.21  fof(f3168,plain,(
% 37.20/5.21    spl2_197 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k1_xboole_0 = k7_subset_1(X0,X0,X1))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_197])])).
% 37.20/5.21  fof(f3237,plain,(
% 37.20/5.21    ( ! [X4,X3] : (k1_xboole_0 = k7_subset_1(X3,X3,k3_tarski(k2_tarski(X4,X3)))) ) | (~spl2_130 | ~spl2_197)),
% 37.20/5.21    inference(resolution,[],[f3169,f1524])).
% 37.20/5.21  fof(f1524,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ) | ~spl2_130),
% 37.20/5.21    inference(avatar_component_clause,[],[f1523])).
% 37.20/5.21  fof(f3169,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k7_subset_1(X0,X0,X1)) ) | ~spl2_197),
% 37.20/5.21    inference(avatar_component_clause,[],[f3168])).
% 37.20/5.21  fof(f3346,plain,(
% 37.20/5.21    spl2_202 | ~spl2_131 | ~spl2_197),
% 37.20/5.21    inference(avatar_split_clause,[],[f3236,f3168,f1558,f3344])).
% 37.20/5.21  fof(f3236,plain,(
% 37.20/5.21    ( ! [X2,X1] : (k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2)))) ) | (~spl2_131 | ~spl2_197)),
% 37.20/5.21    inference(resolution,[],[f3169,f1559])).
% 37.20/5.21  fof(f3342,plain,(
% 37.20/5.21    spl2_201 | ~spl2_56 | ~spl2_66 | ~spl2_151),
% 37.20/5.21    inference(avatar_split_clause,[],[f2631,f2292,f600,f497,f3340])).
% 37.20/5.21  fof(f2631,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_56 | ~spl2_66 | ~spl2_151)),
% 37.20/5.21    inference(backward_demodulation,[],[f601,f2609])).
% 37.20/5.21  fof(f3170,plain,(
% 37.20/5.21    spl2_197 | ~spl2_23 | ~spl2_193),
% 37.20/5.21    inference(avatar_split_clause,[],[f3133,f3042,f241,f3168])).
% 37.20/5.21  fof(f241,plain,(
% 37.20/5.21    spl2_23 <=> ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1)),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 37.20/5.21  fof(f3042,plain,(
% 37.20/5.21    spl2_193 <=> ! [X1,X0] : (r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) | ~r1_tarski(X0,X1))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).
% 37.20/5.21  fof(f3133,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k7_subset_1(X0,X0,X1)) ) | (~spl2_23 | ~spl2_193)),
% 37.20/5.21    inference(resolution,[],[f3043,f242])).
% 37.20/5.21  fof(f242,plain,(
% 37.20/5.21    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl2_23),
% 37.20/5.21    inference(avatar_component_clause,[],[f241])).
% 37.20/5.21  fof(f3043,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) | ~r1_tarski(X0,X1)) ) | ~spl2_193),
% 37.20/5.21    inference(avatar_component_clause,[],[f3042])).
% 37.20/5.21  fof(f3044,plain,(
% 37.20/5.21    spl2_193 | ~spl2_56 | ~spl2_77 | ~spl2_151 | ~spl2_170),
% 37.20/5.21    inference(avatar_split_clause,[],[f2660,f2566,f2292,f768,f497,f3042])).
% 37.20/5.21  fof(f2566,plain,(
% 37.20/5.21    spl2_170 <=> ! [X1,X0] : (r1_tarski(X1,k3_tarski(k2_tarski(X0,k1_xboole_0))) | ~r1_tarski(X1,X0))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_170])])).
% 37.20/5.21  fof(f2660,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) | ~r1_tarski(X0,X1)) ) | (~spl2_56 | ~spl2_77 | ~spl2_151 | ~spl2_170)),
% 37.20/5.21    inference(backward_demodulation,[],[f2577,f2609])).
% 37.20/5.21  fof(f2577,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_xboole_0)) ) | (~spl2_77 | ~spl2_170)),
% 37.20/5.21    inference(resolution,[],[f2567,f769])).
% 37.20/5.21  fof(f2567,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(X1,k3_tarski(k2_tarski(X0,k1_xboole_0))) | ~r1_tarski(X1,X0)) ) | ~spl2_170),
% 37.20/5.21    inference(avatar_component_clause,[],[f2566])).
% 37.20/5.21  fof(f2841,plain,(
% 37.20/5.21    spl2_181 | ~spl2_20 | ~spl2_56 | ~spl2_151),
% 37.20/5.21    inference(avatar_split_clause,[],[f2625,f2292,f497,f213,f2839])).
% 37.20/5.21  fof(f213,plain,(
% 37.20/5.21    spl2_20 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 37.20/5.21  fof(f2625,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~r1_tarski(X0,k7_subset_1(X1,X1,X0)) | k1_xboole_0 = X0) ) | (~spl2_20 | ~spl2_56 | ~spl2_151)),
% 37.20/5.21    inference(backward_demodulation,[],[f214,f2609])).
% 37.20/5.21  fof(f214,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) | k1_xboole_0 = X0) ) | ~spl2_20),
% 37.20/5.21    inference(avatar_component_clause,[],[f213])).
% 37.20/5.21  fof(f2790,plain,(
% 37.20/5.21    spl2_176 | ~spl2_35 | ~spl2_175),
% 37.20/5.21    inference(avatar_split_clause,[],[f2784,f2781,f328,f2787])).
% 37.20/5.21  fof(f328,plain,(
% 37.20/5.21    spl2_35 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 37.20/5.21  fof(f2784,plain,(
% 37.20/5.21    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_35 | ~spl2_175)),
% 37.20/5.21    inference(superposition,[],[f2782,f330])).
% 37.20/5.21  fof(f330,plain,(
% 37.20/5.21    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_35),
% 37.20/5.21    inference(avatar_component_clause,[],[f328])).
% 37.20/5.21  fof(f2783,plain,(
% 37.20/5.21    spl2_175 | ~spl2_4 | ~spl2_56 | ~spl2_151),
% 37.20/5.21    inference(avatar_split_clause,[],[f2743,f2292,f497,f122,f2781])).
% 37.20/5.21  fof(f2743,plain,(
% 37.20/5.21    ( ! [X21] : (k7_subset_1(u1_struct_0(sK0),sK1,X21) = k7_subset_1(sK1,sK1,X21)) ) | (~spl2_4 | ~spl2_56 | ~spl2_151)),
% 37.20/5.21    inference(forward_demodulation,[],[f2622,f2609])).
% 37.20/5.21  fof(f2622,plain,(
% 37.20/5.21    ( ! [X21] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X21))) = k7_subset_1(u1_struct_0(sK0),sK1,X21)) ) | (~spl2_4 | ~spl2_151)),
% 37.20/5.21    inference(resolution,[],[f2293,f124])).
% 37.20/5.21  fof(f2756,plain,(
% 37.20/5.21    spl2_173 | ~spl2_12 | ~spl2_56 | ~spl2_151),
% 37.20/5.21    inference(avatar_split_clause,[],[f2624,f2292,f497,f162,f2754])).
% 37.20/5.21  fof(f162,plain,(
% 37.20/5.21    spl2_12 <=> ! [X1,X0] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 37.20/5.21  fof(f2624,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) ) | (~spl2_12 | ~spl2_56 | ~spl2_151)),
% 37.20/5.21    inference(backward_demodulation,[],[f163,f2609])).
% 37.20/5.21  fof(f163,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) ) | ~spl2_12),
% 37.20/5.21    inference(avatar_component_clause,[],[f162])).
% 37.20/5.21  fof(f2568,plain,(
% 37.20/5.21    spl2_170 | ~spl2_7 | ~spl2_167),
% 37.20/5.21    inference(avatar_split_clause,[],[f2548,f2523,f135,f2566])).
% 37.20/5.21  fof(f2523,plain,(
% 37.20/5.21    spl2_167 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,X1))))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_167])])).
% 37.20/5.21  fof(f2548,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(X1,k3_tarski(k2_tarski(X0,k1_xboole_0))) | ~r1_tarski(X1,X0)) ) | (~spl2_7 | ~spl2_167)),
% 37.20/5.21    inference(superposition,[],[f2524,f136])).
% 37.20/5.21  fof(f2524,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,X1))) | ~r1_tarski(X0,X1)) ) | ~spl2_167),
% 37.20/5.21    inference(avatar_component_clause,[],[f2523])).
% 37.20/5.21  fof(f2525,plain,(
% 37.20/5.21    spl2_167 | ~spl2_5 | ~spl2_6 | ~spl2_88),
% 37.20/5.21    inference(avatar_split_clause,[],[f1490,f902,f131,f127,f2523])).
% 37.20/5.21  fof(f127,plain,(
% 37.20/5.21    spl2_5 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 37.20/5.21  fof(f131,plain,(
% 37.20/5.21    spl2_6 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 37.20/5.21  fof(f902,plain,(
% 37.20/5.21    spl2_88 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 37.20/5.21  fof(f1490,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,X1)))) ) | (~spl2_5 | ~spl2_6 | ~spl2_88)),
% 37.20/5.21    inference(forward_demodulation,[],[f1487,f128])).
% 37.20/5.21  fof(f128,plain,(
% 37.20/5.21    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_5),
% 37.20/5.21    inference(avatar_component_clause,[],[f127])).
% 37.20/5.21  fof(f1487,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~r1_tarski(k5_xboole_0(X0,k1_xboole_0),X1) | r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,X1)))) ) | (~spl2_6 | ~spl2_88)),
% 37.20/5.21    inference(superposition,[],[f903,f132])).
% 37.20/5.21  fof(f132,plain,(
% 37.20/5.21    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) ) | ~spl2_6),
% 37.20/5.21    inference(avatar_component_clause,[],[f131])).
% 37.20/5.21  fof(f903,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) ) | ~spl2_88),
% 37.20/5.21    inference(avatar_component_clause,[],[f902])).
% 37.20/5.21  fof(f2294,plain,(
% 37.20/5.21    spl2_151),
% 37.20/5.21    inference(avatar_split_clause,[],[f101,f2292])).
% 37.20/5.21  fof(f101,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.21    inference(definition_unfolding,[],[f88,f93])).
% 37.20/5.21  fof(f88,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f46])).
% 37.20/5.21  fof(f46,plain,(
% 37.20/5.21    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    inference(ennf_transformation,[],[f18])).
% 37.20/5.21  fof(f18,axiom,(
% 37.20/5.21    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 37.20/5.21  fof(f2152,plain,(
% 37.20/5.21    spl2_138),
% 37.20/5.21    inference(avatar_split_clause,[],[f70,f2150])).
% 37.20/5.21  fof(f70,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f36])).
% 37.20/5.21  fof(f36,plain,(
% 37.20/5.21    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 37.20/5.21    inference(flattening,[],[f35])).
% 37.20/5.21  fof(f35,plain,(
% 37.20/5.21    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 37.20/5.21    inference(ennf_transformation,[],[f22])).
% 37.20/5.21  fof(f22,axiom,(
% 37.20/5.21    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 37.20/5.21  fof(f2131,plain,(
% 37.20/5.21    spl2_137 | ~spl2_17 | ~spl2_56 | ~spl2_136),
% 37.20/5.21    inference(avatar_split_clause,[],[f2127,f2122,f497,f199,f2129])).
% 37.20/5.21  fof(f199,plain,(
% 37.20/5.21    spl2_17 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 37.20/5.21  fof(f2122,plain,(
% 37.20/5.21    spl2_136 <=> ! [X18] : k1_xboole_0 = k3_subset_1(X18,X18)),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).
% 37.20/5.21  fof(f2127,plain,(
% 37.20/5.21    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) ) | (~spl2_17 | ~spl2_56 | ~spl2_136)),
% 37.20/5.21    inference(subsumption_resolution,[],[f2126,f498])).
% 37.20/5.21  fof(f2126,plain,(
% 37.20/5.21    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) ) | (~spl2_17 | ~spl2_136)),
% 37.20/5.21    inference(superposition,[],[f200,f2123])).
% 37.20/5.21  fof(f2123,plain,(
% 37.20/5.21    ( ! [X18] : (k1_xboole_0 = k3_subset_1(X18,X18)) ) | ~spl2_136),
% 37.20/5.21    inference(avatar_component_clause,[],[f2122])).
% 37.20/5.21  fof(f200,plain,(
% 37.20/5.21    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_17),
% 37.20/5.21    inference(avatar_component_clause,[],[f199])).
% 37.20/5.21  fof(f2124,plain,(
% 37.20/5.21    spl2_136 | ~spl2_20 | ~spl2_132),
% 37.20/5.21    inference(avatar_split_clause,[],[f1605,f1595,f213,f2122])).
% 37.20/5.21  fof(f1595,plain,(
% 37.20/5.21    spl2_132 <=> ! [X1,X0] : r1_tarski(k3_subset_1(X0,X0),X1)),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).
% 37.20/5.21  fof(f1605,plain,(
% 37.20/5.21    ( ! [X18] : (k1_xboole_0 = k3_subset_1(X18,X18)) ) | (~spl2_20 | ~spl2_132)),
% 37.20/5.21    inference(resolution,[],[f1596,f214])).
% 37.20/5.21  fof(f1596,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X0),X1)) ) | ~spl2_132),
% 37.20/5.21    inference(avatar_component_clause,[],[f1595])).
% 37.20/5.21  fof(f2118,plain,(
% 37.20/5.21    spl2_135 | ~spl2_20 | ~spl2_24 | ~spl2_132),
% 37.20/5.21    inference(avatar_split_clause,[],[f1622,f1595,f251,f213,f2116])).
% 37.20/5.21  fof(f251,plain,(
% 37.20/5.21    spl2_24 <=> ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 37.20/5.21  fof(f1622,plain,(
% 37.20/5.21    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | (~spl2_20 | ~spl2_24 | ~spl2_132)),
% 37.20/5.21    inference(backward_demodulation,[],[f252,f1605])).
% 37.20/5.21  fof(f252,plain,(
% 37.20/5.21    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) ) | ~spl2_24),
% 37.20/5.21    inference(avatar_component_clause,[],[f251])).
% 37.20/5.21  fof(f1597,plain,(
% 37.20/5.21    spl2_132 | ~spl2_77 | ~spl2_121 | ~spl2_131),
% 37.20/5.21    inference(avatar_split_clause,[],[f1592,f1558,f1389,f768,f1595])).
% 37.20/5.21  fof(f1389,plain,(
% 37.20/5.21    spl2_121 <=> ! [X2] : k3_subset_1(X2,X2) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).
% 37.20/5.21  fof(f1592,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X0),X1)) ) | (~spl2_77 | ~spl2_121 | ~spl2_131)),
% 37.20/5.21    inference(forward_demodulation,[],[f1561,f1390])).
% 37.20/5.21  fof(f1390,plain,(
% 37.20/5.21    ( ! [X2] : (k3_subset_1(X2,X2) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))) ) | ~spl2_121),
% 37.20/5.21    inference(avatar_component_clause,[],[f1389])).
% 37.20/5.21  fof(f1561,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))),X1)) ) | (~spl2_77 | ~spl2_131)),
% 37.20/5.21    inference(resolution,[],[f1559,f769])).
% 37.20/5.21  fof(f1560,plain,(
% 37.20/5.21    spl2_131 | ~spl2_7 | ~spl2_130),
% 37.20/5.21    inference(avatar_split_clause,[],[f1553,f1523,f135,f1558])).
% 37.20/5.21  fof(f1553,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) ) | (~spl2_7 | ~spl2_130)),
% 37.20/5.21    inference(superposition,[],[f1524,f136])).
% 37.20/5.21  fof(f1525,plain,(
% 37.20/5.21    spl2_130 | ~spl2_12 | ~spl2_88),
% 37.20/5.21    inference(avatar_split_clause,[],[f1474,f902,f162,f1523])).
% 37.20/5.21  fof(f1474,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ) | (~spl2_12 | ~spl2_88)),
% 37.20/5.21    inference(resolution,[],[f903,f163])).
% 37.20/5.21  fof(f1391,plain,(
% 37.20/5.21    spl2_121 | ~spl2_56 | ~spl2_66),
% 37.20/5.21    inference(avatar_split_clause,[],[f1228,f600,f497,f1389])).
% 37.20/5.21  fof(f1228,plain,(
% 37.20/5.21    ( ! [X2] : (k3_subset_1(X2,X2) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))) ) | (~spl2_56 | ~spl2_66)),
% 37.20/5.21    inference(resolution,[],[f601,f498])).
% 37.20/5.21  fof(f1174,plain,(
% 37.20/5.21    spl2_103 | ~spl2_4 | ~spl2_102),
% 37.20/5.21    inference(avatar_split_clause,[],[f1166,f1163,f122,f1171])).
% 37.20/5.21  fof(f1163,plain,(
% 37.20/5.21    spl2_102 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).
% 37.20/5.21  fof(f1166,plain,(
% 37.20/5.21    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_102)),
% 37.20/5.21    inference(resolution,[],[f1164,f124])).
% 37.20/5.21  fof(f1164,plain,(
% 37.20/5.21    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_102),
% 37.20/5.21    inference(avatar_component_clause,[],[f1163])).
% 37.20/5.21  fof(f1165,plain,(
% 37.20/5.21    spl2_102 | ~spl2_2 | ~spl2_55),
% 37.20/5.21    inference(avatar_split_clause,[],[f1161,f484,f113,f1163])).
% 37.20/5.21  fof(f484,plain,(
% 37.20/5.21    spl2_55 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 37.20/5.21  fof(f1161,plain,(
% 37.20/5.21    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_55)),
% 37.20/5.21    inference(resolution,[],[f485,f115])).
% 37.20/5.21  fof(f485,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl2_55),
% 37.20/5.21    inference(avatar_component_clause,[],[f484])).
% 37.20/5.21  fof(f904,plain,(
% 37.20/5.21    spl2_88),
% 37.20/5.21    inference(avatar_split_clause,[],[f103,f902])).
% 37.20/5.21  fof(f103,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)) )),
% 37.20/5.21    inference(definition_unfolding,[],[f90,f75,f93])).
% 37.20/5.21  fof(f90,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f48])).
% 37.20/5.21  fof(f48,plain,(
% 37.20/5.21    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 37.20/5.21    inference(ennf_transformation,[],[f8])).
% 37.20/5.21  fof(f8,axiom,(
% 37.20/5.21    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 37.20/5.21  fof(f770,plain,(
% 37.20/5.21    spl2_77),
% 37.20/5.21    inference(avatar_split_clause,[],[f102,f768])).
% 37.20/5.21  fof(f102,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 37.20/5.21    inference(definition_unfolding,[],[f89,f93,f75])).
% 37.20/5.21  fof(f89,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f47])).
% 37.20/5.21  fof(f47,plain,(
% 37.20/5.21    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 37.20/5.21    inference(ennf_transformation,[],[f7])).
% 37.20/5.21  fof(f7,axiom,(
% 37.20/5.21    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 37.20/5.21  fof(f602,plain,(
% 37.20/5.21    spl2_66),
% 37.20/5.21    inference(avatar_split_clause,[],[f99,f600])).
% 37.20/5.21  fof(f99,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.21    inference(definition_unfolding,[],[f80,f93])).
% 37.20/5.21  fof(f80,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f38])).
% 37.20/5.21  fof(f38,plain,(
% 37.20/5.21    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    inference(ennf_transformation,[],[f14])).
% 37.20/5.21  fof(f14,axiom,(
% 37.20/5.21    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 37.20/5.21  fof(f499,plain,(
% 37.20/5.21    spl2_56 | ~spl2_13 | ~spl2_29 | ~spl2_54),
% 37.20/5.21    inference(avatar_split_clause,[],[f495,f480,f290,f172,f497])).
% 37.20/5.21  fof(f290,plain,(
% 37.20/5.21    spl2_29 <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1)) | ~r1_tarski(k3_subset_1(X1,X1),X1))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 37.20/5.21  fof(f480,plain,(
% 37.20/5.21    spl2_54 <=> ! [X1,X0] : (r1_tarski(k3_subset_1(X0,X0),X1) | ~r1_tarski(X0,X1))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 37.20/5.21  fof(f495,plain,(
% 37.20/5.21    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1))) ) | (~spl2_13 | ~spl2_29 | ~spl2_54)),
% 37.20/5.21    inference(subsumption_resolution,[],[f291,f487])).
% 37.20/5.21  fof(f487,plain,(
% 37.20/5.21    ( ! [X0] : (r1_tarski(k3_subset_1(X0,X0),X0)) ) | (~spl2_13 | ~spl2_54)),
% 37.20/5.21    inference(resolution,[],[f481,f173])).
% 37.20/5.21  fof(f481,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_subset_1(X0,X0),X1)) ) | ~spl2_54),
% 37.20/5.21    inference(avatar_component_clause,[],[f480])).
% 37.20/5.21  fof(f291,plain,(
% 37.20/5.21    ( ! [X1] : (~r1_tarski(k3_subset_1(X1,X1),X1) | m1_subset_1(X1,k1_zfmisc_1(X1))) ) | ~spl2_29),
% 37.20/5.21    inference(avatar_component_clause,[],[f290])).
% 37.20/5.21  fof(f486,plain,(
% 37.20/5.21    spl2_55),
% 37.20/5.21    inference(avatar_split_clause,[],[f85,f484])).
% 37.20/5.21  fof(f85,plain,(
% 37.20/5.21    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f45])).
% 37.20/5.21  fof(f45,plain,(
% 37.20/5.21    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 37.20/5.21    inference(flattening,[],[f44])).
% 37.20/5.21  fof(f44,plain,(
% 37.20/5.21    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 37.20/5.21    inference(ennf_transformation,[],[f23])).
% 37.20/5.21  fof(f23,axiom,(
% 37.20/5.21    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 37.20/5.21  fof(f482,plain,(
% 37.20/5.21    spl2_54 | ~spl2_13 | ~spl2_53),
% 37.20/5.21    inference(avatar_split_clause,[],[f470,f467,f172,f480])).
% 37.20/5.21  fof(f467,plain,(
% 37.20/5.21    spl2_53 <=> ! [X1,X3,X2] : (~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X1,X3),X2) | ~r1_tarski(X3,X1))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 37.20/5.21  fof(f470,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X0),X1) | ~r1_tarski(X0,X1)) ) | (~spl2_13 | ~spl2_53)),
% 37.20/5.21    inference(resolution,[],[f468,f173])).
% 37.20/5.21  fof(f468,plain,(
% 37.20/5.21    ( ! [X2,X3,X1] : (~r1_tarski(X3,X1) | r1_tarski(k3_subset_1(X1,X3),X2) | ~r1_tarski(X1,X2)) ) | ~spl2_53),
% 37.20/5.21    inference(avatar_component_clause,[],[f467])).
% 37.20/5.21  fof(f469,plain,(
% 37.20/5.21    spl2_53 | ~spl2_9 | ~spl2_49),
% 37.20/5.21    inference(avatar_split_clause,[],[f443,f439,f143,f467])).
% 37.20/5.21  fof(f439,plain,(
% 37.20/5.21    spl2_49 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X1,X0),X2))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 37.20/5.21  fof(f443,plain,(
% 37.20/5.21    ( ! [X2,X3,X1] : (~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X1,X3),X2) | ~r1_tarski(X3,X1)) ) | (~spl2_9 | ~spl2_49)),
% 37.20/5.21    inference(resolution,[],[f440,f144])).
% 37.20/5.21  fof(f440,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X1,X0),X2)) ) | ~spl2_49),
% 37.20/5.21    inference(avatar_component_clause,[],[f439])).
% 37.20/5.21  fof(f441,plain,(
% 37.20/5.21    spl2_49 | ~spl2_15 | ~spl2_18),
% 37.20/5.21    inference(avatar_split_clause,[],[f207,f204,f186,f439])).
% 37.20/5.21  fof(f204,plain,(
% 37.20/5.21    spl2_18 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k3_subset_1(X1,X0),X1))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 37.20/5.21  fof(f207,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X1,X0),X2)) ) | (~spl2_15 | ~spl2_18)),
% 37.20/5.21    inference(resolution,[],[f205,f187])).
% 37.20/5.21  fof(f205,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl2_18),
% 37.20/5.21    inference(avatar_component_clause,[],[f204])).
% 37.20/5.21  fof(f411,plain,(
% 37.20/5.21    spl2_45 | ~spl2_9 | ~spl2_42),
% 37.20/5.21    inference(avatar_split_clause,[],[f397,f390,f143,f409])).
% 37.20/5.21  fof(f390,plain,(
% 37.20/5.21    spl2_42 <=> ! [X1,X0] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 37.20/5.21  fof(f397,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~r1_tarski(X1,X0)) ) | (~spl2_9 | ~spl2_42)),
% 37.20/5.21    inference(resolution,[],[f391,f144])).
% 37.20/5.21  fof(f391,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) ) | ~spl2_42),
% 37.20/5.21    inference(avatar_component_clause,[],[f390])).
% 37.20/5.21  fof(f407,plain,(
% 37.20/5.21    spl2_44),
% 37.20/5.21    inference(avatar_split_clause,[],[f84,f405])).
% 37.20/5.21  fof(f84,plain,(
% 37.20/5.21    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f43])).
% 37.20/5.21  fof(f43,plain,(
% 37.20/5.21    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 37.20/5.21    inference(flattening,[],[f42])).
% 37.20/5.21  fof(f42,plain,(
% 37.20/5.21    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 37.20/5.21    inference(ennf_transformation,[],[f24])).
% 37.20/5.21  fof(f24,axiom,(
% 37.20/5.21    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 37.20/5.21  fof(f392,plain,(
% 37.20/5.21    spl2_42),
% 37.20/5.21    inference(avatar_split_clause,[],[f106,f390])).
% 37.20/5.21  fof(f106,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.21    inference(forward_demodulation,[],[f82,f64])).
% 37.20/5.21  fof(f64,plain,(
% 37.20/5.21    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 37.20/5.21    inference(cnf_transformation,[],[f13])).
% 37.20/5.21  fof(f13,axiom,(
% 37.20/5.21    ! [X0] : k2_subset_1(X0) = X0),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 37.20/5.21  fof(f82,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f40])).
% 37.20/5.21  fof(f40,plain,(
% 37.20/5.21    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    inference(ennf_transformation,[],[f19])).
% 37.20/5.21  fof(f19,axiom,(
% 37.20/5.21    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 37.20/5.21  fof(f388,plain,(
% 37.20/5.21    spl2_41),
% 37.20/5.21    inference(avatar_split_clause,[],[f98,f386])).
% 37.20/5.21  fof(f98,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 37.20/5.21    inference(definition_unfolding,[],[f77,f75,f75,f75])).
% 37.20/5.21  fof(f77,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f10])).
% 37.20/5.21  fof(f10,axiom,(
% 37.20/5.21    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 37.20/5.21  fof(f331,plain,(
% 37.20/5.21    spl2_34 | spl2_35),
% 37.20/5.21    inference(avatar_split_clause,[],[f62,f328,f324])).
% 37.20/5.21  fof(f62,plain,(
% 37.20/5.21    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 37.20/5.21    inference(cnf_transformation,[],[f57])).
% 37.20/5.21  fof(f292,plain,(
% 37.20/5.21    spl2_29 | ~spl2_9 | ~spl2_28),
% 37.20/5.21    inference(avatar_split_clause,[],[f287,f283,f143,f290])).
% 37.20/5.21  fof(f283,plain,(
% 37.20/5.21    spl2_28 <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1)) | ~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 37.20/5.21  fof(f287,plain,(
% 37.20/5.21    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1)) | ~r1_tarski(k3_subset_1(X1,X1),X1)) ) | (~spl2_9 | ~spl2_28)),
% 37.20/5.21    inference(resolution,[],[f284,f144])).
% 37.20/5.21  fof(f284,plain,(
% 37.20/5.21    ( ! [X1] : (~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) | m1_subset_1(X1,k1_zfmisc_1(X1))) ) | ~spl2_28),
% 37.20/5.21    inference(avatar_component_clause,[],[f283])).
% 37.20/5.21  fof(f285,plain,(
% 37.20/5.21    spl2_28 | ~spl2_17 | ~spl2_24),
% 37.20/5.21    inference(avatar_split_clause,[],[f255,f251,f199,f283])).
% 37.20/5.21  fof(f255,plain,(
% 37.20/5.21    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1)) | ~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))) ) | (~spl2_17 | ~spl2_24)),
% 37.20/5.21    inference(superposition,[],[f200,f252])).
% 37.20/5.21  fof(f253,plain,(
% 37.20/5.21    spl2_24 | ~spl2_13 | ~spl2_22),
% 37.20/5.21    inference(avatar_split_clause,[],[f230,f227,f172,f251])).
% 37.20/5.21  fof(f230,plain,(
% 37.20/5.21    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) ) | (~spl2_13 | ~spl2_22)),
% 37.20/5.21    inference(resolution,[],[f228,f173])).
% 37.20/5.21  fof(f243,plain,(
% 37.20/5.21    spl2_23 | ~spl2_5 | ~spl2_10 | ~spl2_20),
% 37.20/5.21    inference(avatar_split_clause,[],[f239,f213,f149,f127,f241])).
% 37.20/5.21  fof(f149,plain,(
% 37.20/5.21    spl2_10 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 37.20/5.21  fof(f239,plain,(
% 37.20/5.21    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | (~spl2_5 | ~spl2_10 | ~spl2_20)),
% 37.20/5.21    inference(forward_demodulation,[],[f238,f128])).
% 37.20/5.21  fof(f238,plain,(
% 37.20/5.21    ( ! [X1] : (~r1_tarski(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = X1) ) | (~spl2_10 | ~spl2_20)),
% 37.20/5.21    inference(superposition,[],[f214,f150])).
% 37.20/5.21  fof(f150,plain,(
% 37.20/5.21    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ) | ~spl2_10),
% 37.20/5.21    inference(avatar_component_clause,[],[f149])).
% 37.20/5.21  fof(f229,plain,(
% 37.20/5.21    spl2_22 | ~spl2_9 | ~spl2_19),
% 37.20/5.21    inference(avatar_split_clause,[],[f217,f209,f143,f227])).
% 37.20/5.21  fof(f209,plain,(
% 37.20/5.21    spl2_19 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 37.20/5.21  fof(f217,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~r1_tarski(X1,X0)) ) | (~spl2_9 | ~spl2_19)),
% 37.20/5.21    inference(resolution,[],[f210,f144])).
% 37.20/5.21  fof(f210,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl2_19),
% 37.20/5.21    inference(avatar_component_clause,[],[f209])).
% 37.20/5.21  fof(f215,plain,(
% 37.20/5.21    spl2_20),
% 37.20/5.21    inference(avatar_split_clause,[],[f100,f213])).
% 37.20/5.21  fof(f100,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 37.20/5.21    inference(definition_unfolding,[],[f83,f93])).
% 37.20/5.21  fof(f83,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f41])).
% 37.20/5.21  fof(f41,plain,(
% 37.20/5.21    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 37.20/5.21    inference(ennf_transformation,[],[f5])).
% 37.20/5.21  fof(f5,axiom,(
% 37.20/5.21    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 37.20/5.21  fof(f211,plain,(
% 37.20/5.21    spl2_19),
% 37.20/5.21    inference(avatar_split_clause,[],[f81,f209])).
% 37.20/5.21  fof(f81,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f39])).
% 37.20/5.21  fof(f39,plain,(
% 37.20/5.21    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    inference(ennf_transformation,[],[f16])).
% 37.20/5.21  fof(f16,axiom,(
% 37.20/5.21    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 37.20/5.21  fof(f206,plain,(
% 37.20/5.21    spl2_18 | ~spl2_8 | ~spl2_17),
% 37.20/5.21    inference(avatar_split_clause,[],[f202,f199,f139,f204])).
% 37.20/5.21  fof(f139,plain,(
% 37.20/5.21    spl2_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 37.20/5.21    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 37.20/5.21  fof(f202,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k3_subset_1(X1,X0),X1)) ) | (~spl2_8 | ~spl2_17)),
% 37.20/5.21    inference(resolution,[],[f200,f140])).
% 37.20/5.21  fof(f140,plain,(
% 37.20/5.21    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_8),
% 37.20/5.21    inference(avatar_component_clause,[],[f139])).
% 37.20/5.21  fof(f201,plain,(
% 37.20/5.21    spl2_17),
% 37.20/5.21    inference(avatar_split_clause,[],[f79,f199])).
% 37.20/5.21  fof(f79,plain,(
% 37.20/5.21    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f37])).
% 37.20/5.21  fof(f37,plain,(
% 37.20/5.21    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 37.20/5.21    inference(ennf_transformation,[],[f15])).
% 37.20/5.21  fof(f15,axiom,(
% 37.20/5.21    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 37.20/5.21  fof(f188,plain,(
% 37.20/5.21    spl2_15),
% 37.20/5.21    inference(avatar_split_clause,[],[f91,f186])).
% 37.20/5.21  fof(f91,plain,(
% 37.20/5.21    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f50])).
% 37.20/5.21  fof(f50,plain,(
% 37.20/5.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 37.20/5.21    inference(flattening,[],[f49])).
% 37.20/5.21  fof(f49,plain,(
% 37.20/5.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 37.20/5.21    inference(ennf_transformation,[],[f2])).
% 37.20/5.21  fof(f2,axiom,(
% 37.20/5.21    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 37.20/5.21  fof(f174,plain,(
% 37.20/5.21    spl2_13 | ~spl2_5 | ~spl2_6 | ~spl2_12),
% 37.20/5.21    inference(avatar_split_clause,[],[f169,f162,f131,f127,f172])).
% 37.20/5.21  fof(f169,plain,(
% 37.20/5.21    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl2_5 | ~spl2_6 | ~spl2_12)),
% 37.20/5.21    inference(forward_demodulation,[],[f167,f128])).
% 37.20/5.21  fof(f167,plain,(
% 37.20/5.21    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) ) | (~spl2_6 | ~spl2_12)),
% 37.20/5.21    inference(superposition,[],[f163,f132])).
% 37.20/5.21  fof(f164,plain,(
% 37.20/5.21    spl2_12),
% 37.20/5.21    inference(avatar_split_clause,[],[f96,f162])).
% 37.20/5.21  fof(f96,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 37.20/5.21    inference(definition_unfolding,[],[f72,f93])).
% 37.20/5.21  fof(f72,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f4])).
% 37.20/5.21  fof(f4,axiom,(
% 37.20/5.21    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 37.20/5.21  fof(f151,plain,(
% 37.20/5.21    spl2_10 | ~spl2_6 | ~spl2_7),
% 37.20/5.21    inference(avatar_split_clause,[],[f146,f135,f131,f149])).
% 37.20/5.21  fof(f146,plain,(
% 37.20/5.21    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ) | (~spl2_6 | ~spl2_7)),
% 37.20/5.21    inference(superposition,[],[f132,f136])).
% 37.20/5.21  fof(f145,plain,(
% 37.20/5.21    spl2_9),
% 37.20/5.21    inference(avatar_split_clause,[],[f87,f143])).
% 37.20/5.21  fof(f87,plain,(
% 37.20/5.21    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f58])).
% 37.20/5.21  fof(f58,plain,(
% 37.20/5.21    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 37.20/5.21    inference(nnf_transformation,[],[f21])).
% 37.20/5.21  fof(f21,axiom,(
% 37.20/5.21    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 37.20/5.21  fof(f141,plain,(
% 37.20/5.21    spl2_8),
% 37.20/5.21    inference(avatar_split_clause,[],[f86,f139])).
% 37.20/5.21  fof(f86,plain,(
% 37.20/5.21    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 37.20/5.21    inference(cnf_transformation,[],[f58])).
% 37.20/5.21  fof(f137,plain,(
% 37.20/5.21    spl2_7),
% 37.20/5.21    inference(avatar_split_clause,[],[f73,f135])).
% 37.20/5.21  fof(f73,plain,(
% 37.20/5.21    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f11])).
% 37.20/5.21  fof(f11,axiom,(
% 37.20/5.21    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 37.20/5.21  fof(f133,plain,(
% 37.20/5.21    spl2_6),
% 37.20/5.21    inference(avatar_split_clause,[],[f94,f131])).
% 37.20/5.21  fof(f94,plain,(
% 37.20/5.21    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 37.20/5.21    inference(definition_unfolding,[],[f65,f74])).
% 37.20/5.21  fof(f65,plain,(
% 37.20/5.21    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 37.20/5.21    inference(cnf_transformation,[],[f3])).
% 37.20/5.21  fof(f3,axiom,(
% 37.20/5.21    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 37.20/5.21  fof(f129,plain,(
% 37.20/5.21    spl2_5),
% 37.20/5.21    inference(avatar_split_clause,[],[f105,f127])).
% 37.20/5.21  fof(f105,plain,(
% 37.20/5.21    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 37.20/5.21    inference(forward_demodulation,[],[f95,f94])).
% 37.20/5.21  fof(f95,plain,(
% 37.20/5.21    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 37.20/5.21    inference(definition_unfolding,[],[f66,f93])).
% 37.20/5.21  fof(f66,plain,(
% 37.20/5.21    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 37.20/5.21    inference(cnf_transformation,[],[f6])).
% 37.20/5.21  fof(f6,axiom,(
% 37.20/5.21    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 37.20/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 37.20/5.21  fof(f125,plain,(
% 37.20/5.21    spl2_4),
% 37.20/5.21    inference(avatar_split_clause,[],[f61,f122])).
% 37.20/5.21  fof(f61,plain,(
% 37.20/5.21    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 37.20/5.21    inference(cnf_transformation,[],[f57])).
% 37.20/5.21  fof(f116,plain,(
% 37.20/5.21    spl2_2),
% 37.20/5.21    inference(avatar_split_clause,[],[f60,f113])).
% 37.20/5.21  fof(f60,plain,(
% 37.20/5.21    l1_pre_topc(sK0)),
% 37.20/5.21    inference(cnf_transformation,[],[f57])).
% 37.20/5.21  fof(f111,plain,(
% 37.20/5.21    spl2_1),
% 37.20/5.21    inference(avatar_split_clause,[],[f59,f108])).
% 37.20/5.21  fof(f59,plain,(
% 37.20/5.21    v2_pre_topc(sK0)),
% 37.20/5.21    inference(cnf_transformation,[],[f57])).
% 37.20/5.21  % SZS output end Proof for theBenchmark
% 37.20/5.21  % (9209)------------------------------
% 37.20/5.21  % (9209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 37.20/5.21  % (9209)Termination reason: Refutation
% 37.20/5.21  
% 37.20/5.21  % (9209)Memory used [KB]: 75350
% 37.20/5.21  % (9209)Time elapsed: 4.602 s
% 37.20/5.21  % (9209)------------------------------
% 37.20/5.21  % (9209)------------------------------
% 37.20/5.22  % (9041)Success in time 4.858 s
%------------------------------------------------------------------------------
