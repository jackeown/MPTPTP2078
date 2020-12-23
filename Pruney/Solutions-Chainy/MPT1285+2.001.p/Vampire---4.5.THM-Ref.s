%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:05 EST 2020

% Result     : Theorem 3.57s
% Output     : Refutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  334 ( 782 expanded)
%              Number of leaves         :   82 ( 388 expanded)
%              Depth                    :   10
%              Number of atoms          : 1296 (3528 expanded)
%              Number of equality atoms :  109 ( 246 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2745,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f120,f126,f132,f141,f142,f146,f150,f154,f158,f162,f166,f170,f181,f185,f194,f203,f207,f218,f222,f229,f248,f261,f266,f270,f274,f301,f319,f330,f341,f349,f362,f387,f431,f444,f483,f488,f498,f544,f575,f590,f654,f715,f825,f1114,f1500,f1854,f1972,f2194,f2322,f2333,f2403,f2441,f2600,f2605,f2676,f2689,f2696,f2716,f2744])).

fof(f2744,plain,
    ( ~ spl4_130
    | spl4_197
    | ~ spl4_204 ),
    inference(avatar_contradiction_clause,[],[f2743])).

fof(f2743,plain,
    ( $false
    | ~ spl4_130
    | spl4_197
    | ~ spl4_204 ),
    inference(subsumption_resolution,[],[f2599,f2720])).

fof(f2720,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_130
    | ~ spl4_204 ),
    inference(superposition,[],[f1499,f2688])).

fof(f2688,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl4_204 ),
    inference(avatar_component_clause,[],[f2686])).

fof(f2686,plain,
    ( spl4_204
  <=> sK3 = k1_tops_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_204])])).

fof(f1499,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_130 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f1497,plain,
    ( spl4_130
  <=> r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f2599,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | spl4_197 ),
    inference(avatar_component_clause,[],[f2597])).

fof(f2597,plain,
    ( spl4_197
  <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).

fof(f2716,plain,
    ( ~ spl4_13
    | spl4_202 ),
    inference(avatar_contradiction_clause,[],[f2711])).

fof(f2711,plain,
    ( $false
    | ~ spl4_13
    | spl4_202 ),
    inference(unit_resulting_resolution,[],[f149,f2680])).

fof(f2680,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1))
    | spl4_202 ),
    inference(avatar_component_clause,[],[f2678])).

fof(f2678,plain,
    ( spl4_202
  <=> r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).

fof(f149,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_13
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f2696,plain,
    ( ~ spl4_3
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_62
    | spl4_203 ),
    inference(avatar_contradiction_clause,[],[f2695])).

fof(f2695,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_62
    | spl4_203 ),
    inference(subsumption_resolution,[],[f115,f2694])).

fof(f2694,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ spl4_3
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_62
    | spl4_203 ),
    inference(forward_demodulation,[],[f2693,f589])).

fof(f589,plain,
    ( sK3 = k3_xboole_0(sK3,u1_struct_0(sK1))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f587])).

fof(f587,plain,
    ( spl4_62
  <=> sK3 = k3_xboole_0(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f2693,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK3,u1_struct_0(sK1)),sK1)
    | ~ spl4_3
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_59
    | ~ spl4_60
    | spl4_203 ),
    inference(forward_demodulation,[],[f2692,f578])).

fof(f578,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl4_17
    | ~ spl4_60 ),
    inference(superposition,[],[f574,f165])).

fof(f165,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_17
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f574,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl4_60
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f2692,plain,
    ( ~ v3_pre_topc(k3_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ spl4_3
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_59
    | spl4_203 ),
    inference(forward_demodulation,[],[f2691,f571])).

fof(f571,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f545,f180])).

fof(f180,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_19
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f545,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl4_22
    | ~ spl4_59 ),
    inference(unit_resulting_resolution,[],[f543,f202])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f543,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl4_59
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f2691,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3)),sK1)
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_59
    | spl4_203 ),
    inference(unit_resulting_resolution,[],[f100,f543,f2684,f247])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f2684,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | spl4_203 ),
    inference(avatar_component_clause,[],[f2682])).

fof(f2682,plain,
    ( spl4_203
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_203])])).

fof(f100,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f115,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_6
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f2689,plain,
    ( ~ spl4_202
    | ~ spl4_3
    | ~ spl4_203
    | spl4_204
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_54
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_62
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f694,f652,f587,f573,f542,f485,f201,f179,f164,f2686,f2682,f98,f2678])).

fof(f485,plain,
    ( spl4_54
  <=> k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f652,plain,
    ( spl4_68
  <=> ! [X3,X2] :
        ( ~ v4_pre_topc(X2,X3)
        | k2_pre_topc(X3,X2) = X2
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f694,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1))
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_54
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_62
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f693,f589])).

fof(f693,plain,
    ( k1_tops_1(sK1,sK3) = k3_xboole_0(sK3,u1_struct_0(sK1))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1))
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_54
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f692,f578])).

fof(f692,plain,
    ( k1_tops_1(sK1,sK3) = k3_xboole_0(u1_struct_0(sK1),sK3)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1))
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_54
    | ~ spl4_59
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f676,f571])).

fof(f676,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1))
    | ~ spl4_54
    | ~ spl4_68 ),
    inference(superposition,[],[f487,f653])).

fof(f653,plain,
    ( ! [X2,X3] :
        ( k2_pre_topc(X3,X2) = X2
        | ~ v4_pre_topc(X2,X3)
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X3)) )
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f652])).

fof(f487,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f485])).

fof(f2676,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_11
    | ~ spl4_166
    | ~ spl4_38
    | ~ spl4_37
    | ~ spl4_47
    | ~ spl4_193 ),
    inference(avatar_split_clause,[],[f2430,f2319,f428,f328,f338,f1963,f138,f103,f93])).

fof(f93,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f103,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f138,plain,
    ( spl4_11
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1963,plain,
    ( spl4_166
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).

fof(f338,plain,
    ( spl4_38
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f328,plain,
    ( spl4_37
  <=> ! [X1,X0] :
        ( v4_tops_1(X1,X0)
        | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f428,plain,
    ( spl4_47
  <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f2319,plain,
    ( spl4_193
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_193])])).

fof(f2430,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(sK2,sK2)
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_37
    | ~ spl4_47
    | ~ spl4_193 ),
    inference(forward_demodulation,[],[f433,f2321])).

fof(f2321,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_193 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f433,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_37
    | ~ spl4_47 ),
    inference(superposition,[],[f329,f430])).

fof(f430,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f428])).

fof(f329,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
        | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | v4_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f328])).

fof(f2605,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_7
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f2360,f428,f268,f117,f103,f93])).

fof(f117,plain,
    ( spl4_7
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f268,plain,
    ( spl4_32
  <=> ! [X1,X0] :
        ( v6_tops_1(X1,X0)
        | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f2360,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(trivial_inequality_removal,[],[f2204])).

fof(f2204,plain,
    ( sK2 != sK2
    | v6_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(superposition,[],[f269,f430])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
        | v6_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f2600,plain,
    ( ~ spl4_197
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | spl4_48
    | ~ spl4_77 ),
    inference(avatar_split_clause,[],[f2145,f823,f441,f123,f108,f98,f2597])).

fof(f108,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f123,plain,
    ( spl4_8
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f441,plain,
    ( spl4_48
  <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f823,plain,
    ( spl4_77
  <=> ! [X1,X0] :
        ( ~ v4_tops_1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
        | ~ r1_tarski(X0,k1_tops_1(X1,k2_pre_topc(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f2145,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | spl4_48
    | ~ spl4_77 ),
    inference(unit_resulting_resolution,[],[f100,f110,f443,f125,f824])).

fof(f824,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(X1,k2_pre_topc(X1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
        | ~ v4_tops_1(X0,X1) )
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f823])).

fof(f125,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f443,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | spl4_48 ),
    inference(avatar_component_clause,[],[f441])).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f2441,plain,
    ( ~ spl4_2
    | spl4_8
    | ~ spl4_11
    | ~ spl4_22
    | ~ spl4_35
    | ~ spl4_41
    | ~ spl4_159
    | ~ spl4_183 ),
    inference(avatar_contradiction_clause,[],[f2439])).

fof(f2439,plain,
    ( $false
    | ~ spl4_2
    | spl4_8
    | ~ spl4_11
    | ~ spl4_22
    | ~ spl4_35
    | ~ spl4_41
    | ~ spl4_159
    | ~ spl4_183 ),
    inference(subsumption_resolution,[],[f2195,f2438])).

fof(f2438,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | spl4_8
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f127,f139])).

fof(f139,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f127,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | spl4_8 ),
    inference(subsumption_resolution,[],[f58,f124])).

fof(f124,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f58,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v3_pre_topc(X2,sK0) )
                    & v6_tops_1(X2,sK0) )
                  | ( ~ v6_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v3_pre_topc(X2,sK0) )
                  & v6_tops_1(X2,sK0) )
                | ( ~ v6_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v3_pre_topc(X2,sK0) )
                & v6_tops_1(X2,sK0) )
              | ( ~ v6_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v3_pre_topc(sK2,sK0) )
              & v6_tops_1(sK2,sK0) )
            | ( ~ v6_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v3_pre_topc(sK2,sK0) )
            & v6_tops_1(sK2,sK0) )
          | ( ~ v6_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v3_pre_topc(sK2,sK0) )
          & v6_tops_1(sK2,sK0) )
        | ( ~ v6_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

fof(f2195,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_22
    | ~ spl4_35
    | ~ spl4_41
    | ~ spl4_159
    | ~ spl4_183 ),
    inference(forward_demodulation,[],[f2193,f2133])).

fof(f2133,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_22
    | ~ spl4_35
    | ~ spl4_41
    | ~ spl4_159 ),
    inference(forward_demodulation,[],[f377,f1853])).

fof(f1853,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))))
    | ~ spl4_159 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f1851,plain,
    ( spl4_159
  <=> sK2 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_159])])).

fof(f377,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))))
    | ~ spl4_2
    | ~ spl4_22
    | ~ spl4_35
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f366,f370])).

fof(f370,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | ~ spl4_22
    | ~ spl4_41 ),
    inference(unit_resulting_resolution,[],[f361,f202])).

fof(f361,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl4_41
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f366,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))))
    | ~ spl4_2
    | ~ spl4_35
    | ~ spl4_41 ),
    inference(unit_resulting_resolution,[],[f95,f361,f300])).

fof(f300,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl4_35
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f95,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f2193,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl4_183 ),
    inference(avatar_component_clause,[],[f2191])).

fof(f2191,plain,
    ( spl4_183
  <=> v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_183])])).

fof(f2403,plain,
    ( ~ spl4_13
    | spl4_191 ),
    inference(avatar_contradiction_clause,[],[f2398])).

fof(f2398,plain,
    ( $false
    | ~ spl4_13
    | spl4_191 ),
    inference(unit_resulting_resolution,[],[f149,f2313])).

fof(f2313,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | spl4_191 ),
    inference(avatar_component_clause,[],[f2311])).

fof(f2311,plain,
    ( spl4_191
  <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_191])])).

fof(f2333,plain,
    ( ~ spl4_2
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_53
    | ~ spl4_59
    | ~ spl4_60
    | spl4_192 ),
    inference(avatar_contradiction_clause,[],[f2332])).

fof(f2332,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_53
    | ~ spl4_59
    | ~ spl4_60
    | spl4_192 ),
    inference(subsumption_resolution,[],[f135,f2331])).

fof(f2331,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_53
    | ~ spl4_59
    | ~ spl4_60
    | spl4_192 ),
    inference(forward_demodulation,[],[f2330,f482])).

fof(f482,plain,
    ( sK2 = k3_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl4_53
  <=> sK2 = k3_xboole_0(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f2330,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK2,u1_struct_0(sK0)),sK0)
    | ~ spl4_2
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_59
    | ~ spl4_60
    | spl4_192 ),
    inference(forward_demodulation,[],[f2329,f578])).

fof(f2329,plain,
    ( ~ v3_pre_topc(k3_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ spl4_2
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_28
    | ~ spl4_59
    | spl4_192 ),
    inference(forward_demodulation,[],[f2328,f571])).

fof(f2328,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),sK0)
    | ~ spl4_2
    | ~ spl4_28
    | ~ spl4_59
    | spl4_192 ),
    inference(unit_resulting_resolution,[],[f95,f543,f2317,f247])).

fof(f2317,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | spl4_192 ),
    inference(avatar_component_clause,[],[f2315])).

fof(f2315,plain,
    ( spl4_192
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f135,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_10
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f2322,plain,
    ( ~ spl4_191
    | ~ spl4_2
    | ~ spl4_192
    | spl4_193
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_53
    | ~ spl4_55
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f691,f652,f573,f542,f495,f480,f201,f179,f164,f2319,f2315,f93,f2311])).

fof(f495,plain,
    ( spl4_55
  <=> k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f691,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_53
    | ~ spl4_55
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f690,f482])).

fof(f690,plain,
    ( k3_xboole_0(sK2,u1_struct_0(sK0)) = k1_tops_1(sK0,sK2)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_55
    | ~ spl4_59
    | ~ spl4_60
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f689,f578])).

fof(f689,plain,
    ( k1_tops_1(sK0,sK2) = k3_xboole_0(u1_struct_0(sK0),sK2)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl4_19
    | ~ spl4_22
    | ~ spl4_55
    | ~ spl4_59
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f671,f571])).

fof(f671,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl4_55
    | ~ spl4_68 ),
    inference(superposition,[],[f497,f653])).

fof(f497,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f495])).

fof(f2194,plain,
    ( spl4_183
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f716,f713,f103,f93,f88,f2191])).

fof(f88,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f713,plain,
    ( spl4_70
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X0)),X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f716,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_70 ),
    inference(unit_resulting_resolution,[],[f90,f95,f105,f714])).

fof(f714,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X0)),X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_pre_topc(X1) )
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f713])).

fof(f105,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f90,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1972,plain,
    ( ~ spl4_12
    | spl4_166 ),
    inference(avatar_contradiction_clause,[],[f1967])).

fof(f1967,plain,
    ( $false
    | ~ spl4_12
    | spl4_166 ),
    inference(unit_resulting_resolution,[],[f145,f1965])).

fof(f1965,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_166 ),
    inference(avatar_component_clause,[],[f1963])).

fof(f145,plain,
    ( ! [X1] : r1_tarski(X1,X1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_12
  <=> ! [X1] : r1_tarski(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1854,plain,
    ( spl4_159
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_22
    | ~ spl4_30
    | ~ spl4_35
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f378,f359,f299,f259,f201,f117,f103,f93,f1851])).

fof(f259,plain,
    ( spl4_30
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
        | ~ v6_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f378,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_22
    | ~ spl4_30
    | ~ spl4_35
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f377,f285])).

fof(f285,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f95,f119,f105,f260])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
        | ~ v6_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f259])).

fof(f119,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f1500,plain,
    ( spl4_130
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_36
    | ~ spl4_39
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f392,f384,f346,f317,f108,f98,f1497])).

fof(f317,plain,
    ( spl4_36
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f346,plain,
    ( spl4_39
  <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f384,plain,
    ( spl4_42
  <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f392,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_36
    | ~ spl4_39
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f100,f110,f348,f386,f318])).

fof(f318,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f317])).

fof(f386,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f384])).

fof(f348,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f346])).

fof(f1114,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_24
    | ~ spl4_30
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f379,f359,f259,f216,f117,f103,f93,f88,f134])).

fof(f216,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( v3_pre_topc(k1_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f379,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_24
    | ~ spl4_30
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f364,f285])).

fof(f364,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_24
    | ~ spl4_41 ),
    inference(unit_resulting_resolution,[],[f90,f95,f361,f217])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(k1_tops_1(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f825,plain,
    ( spl4_77
    | ~ spl4_20
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f292,f272,f183,f823])).

fof(f183,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f272,plain,
    ( spl4_33
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
        | ~ v4_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( ~ v4_tops_1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
        | ~ r1_tarski(X0,k1_tops_1(X1,k2_pre_topc(X1,X0))) )
    | ~ spl4_20
    | ~ spl4_33 ),
    inference(resolution,[],[f273,f184])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f183])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
        | ~ v4_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f272])).

fof(f715,plain,
    ( spl4_70
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f240,f220,f216,f713])).

fof(f220,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X0)),X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X0)),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(resolution,[],[f221,f217])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f220])).

fof(f654,plain,
    ( spl4_68
    | ~ spl4_16
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f252,f227,f160,f652])).

fof(f160,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f227,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f252,plain,
    ( ! [X2,X3] :
        ( ~ v4_pre_topc(X2,X3)
        | k2_pre_topc(X3,X2) = X2
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X3)) )
    | ~ spl4_16
    | ~ spl4_26 ),
    inference(resolution,[],[f228,f161])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f227])).

fof(f590,plain,
    ( spl4_62
    | ~ spl4_18
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f289,f263,f168,f587])).

fof(f168,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f263,plain,
    ( spl4_31
  <=> r1_tarski(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f289,plain,
    ( sK3 = k3_xboole_0(sK3,u1_struct_0(sK1))
    | ~ spl4_18
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f265,f169])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f265,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f263])).

fof(f575,plain,
    ( spl4_60
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f186,f164,f152,f573])).

fof(f152,plain,
    ( spl4_14
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f186,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(superposition,[],[f165,f153])).

fof(f153,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f544,plain,
    ( spl4_59
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f176,f160,f148,f542])).

fof(f176,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f149,f161])).

fof(f498,plain,
    ( spl4_55
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f315,f299,f201,f103,f93,f495])).

fof(f315,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f302,f208])).

fof(f208,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2)
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f105,f202])).

fof(f302,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_35 ),
    inference(unit_resulting_resolution,[],[f95,f105,f300])).

fof(f488,plain,
    ( spl4_54
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_22
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f314,f299,f201,f108,f98,f485])).

fof(f314,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_22
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f303,f209])).

fof(f209,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK3) = k3_subset_1(u1_struct_0(sK1),sK3)
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f110,f202])).

fof(f303,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_35 ),
    inference(unit_resulting_resolution,[],[f100,f110,f300])).

fof(f483,plain,
    ( spl4_53
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f223,f191,f168,f480])).

fof(f191,plain,
    ( spl4_21
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f223,plain,
    ( sK2 = k3_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f193,f169])).

fof(f193,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f444,plain,
    ( ~ spl4_48
    | ~ spl4_3
    | ~ spl4_5
    | spl4_9
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f286,f268,f129,f108,f98,f441])).

fof(f129,plain,
    ( spl4_9
  <=> v6_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f286,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5
    | spl4_9
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f100,f131,f110,f269])).

fof(f131,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f431,plain,
    ( spl4_47
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f285,f259,f117,f103,f93,f428])).

fof(f387,plain,
    ( spl4_42
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f235,f220,f108,f98,f384])).

fof(f235,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f100,f110,f221])).

fof(f362,plain,
    ( spl4_41
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f234,f220,f103,f93,f359])).

fof(f234,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f95,f105,f221])).

fof(f349,plain,
    ( spl4_39
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f211,f205,f108,f98,f346])).

fof(f205,plain,
    ( spl4_23
  <=> ! [X1,X0] :
        ( r1_tarski(X1,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f211,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(unit_resulting_resolution,[],[f100,f110,f206])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(X1,k2_pre_topc(X0,X1))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f205])).

fof(f341,plain,
    ( spl4_38
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f210,f205,f103,f93,f338])).

fof(f210,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(unit_resulting_resolution,[],[f95,f105,f206])).

fof(f330,plain,(
    spl4_37 ),
    inference(avatar_split_clause,[],[f70,f328])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f319,plain,(
    spl4_36 ),
    inference(avatar_split_clause,[],[f71,f317])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f301,plain,(
    spl4_35 ),
    inference(avatar_split_clause,[],[f61,f299])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f274,plain,(
    spl4_33 ),
    inference(avatar_split_clause,[],[f68,f272])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f270,plain,(
    spl4_32 ),
    inference(avatar_split_clause,[],[f67,f268])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(f266,plain,
    ( spl4_31
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f172,f156,f108,f263])).

fof(f156,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f172,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f110,f157])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f261,plain,(
    spl4_30 ),
    inference(avatar_split_clause,[],[f66,f259])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f248,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f65,f246])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f229,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f62,f227])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f222,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f79,f220])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f218,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f78,f216])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f207,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f60,f205])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f203,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f77,f201])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f194,plain,
    ( spl4_21
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f171,f156,f103,f191])).

fof(f171,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f105,f157])).

fof(f185,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f82,f183])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f181,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f75,f179])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f170,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f76,f168])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f166,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f74,f164])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f162,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f84,f160])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f158,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f83,f156])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f154,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f73,f152])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f150,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f72,f148])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f146,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f85,f144])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f142,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f59,f138,f134,f129])).

fof(f59,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f141,plain,
    ( ~ spl4_10
    | ~ spl4_11
    | spl4_6 ),
    inference(avatar_split_clause,[],[f121,f113,f138,f134])).

fof(f121,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f57,f114])).

fof(f114,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f57,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f132,plain,
    ( ~ spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f56,f117,f129])).

fof(f56,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f126,plain,
    ( spl4_8
    | spl4_7 ),
    inference(avatar_split_clause,[],[f55,f117,f123])).

fof(f55,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f54,f117,f113])).

fof(f54,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f53,f108])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f52,f103])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f51,f98])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (32049)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.49  % (32034)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.52  % (32036)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.21/0.52  % (32039)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.21/0.53  % (32028)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.21/0.53  % (32048)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.21/0.53  % (32038)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.21/0.53  % (32054)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.53  % (32041)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.53  % (32040)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.53  % (32056)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.53  % (32030)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.54  % (32056)Refutation not found, incomplete strategy% (32056)------------------------------
% 1.39/0.54  % (32056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (32056)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (32056)Memory used [KB]: 10874
% 1.39/0.54  % (32056)Time elapsed: 0.115 s
% 1.39/0.54  % (32056)------------------------------
% 1.39/0.54  % (32056)------------------------------
% 1.39/0.54  % (32046)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.54  % (32035)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.54  % (32032)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.54  % (32055)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.55  % (32047)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.55  % (32029)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.55  % (32031)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.39/0.55  % (32044)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.55  % (32044)Refutation not found, incomplete strategy% (32044)------------------------------
% 1.39/0.55  % (32044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (32044)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (32044)Memory used [KB]: 10746
% 1.39/0.55  % (32044)Time elapsed: 0.152 s
% 1.39/0.55  % (32044)------------------------------
% 1.39/0.55  % (32044)------------------------------
% 1.39/0.55  % (32033)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.55  % (32038)Refutation not found, incomplete strategy% (32038)------------------------------
% 1.39/0.55  % (32038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (32038)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (32038)Memory used [KB]: 10874
% 1.39/0.55  % (32038)Time elapsed: 0.146 s
% 1.39/0.55  % (32038)------------------------------
% 1.39/0.55  % (32038)------------------------------
% 1.39/0.55  % (32042)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.56  % (32045)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.56  % (32057)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.56  % (32053)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.56  % (32051)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.57  % (32037)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.57  % (32052)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.58  % (32043)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.58  % (32050)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.55/0.70  % (32058)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.55/0.71  % (32060)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.55/0.71  % (32031)Refutation not found, incomplete strategy% (32031)------------------------------
% 2.55/0.71  % (32031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.71  % (32031)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.71  
% 2.55/0.71  % (32031)Memory used [KB]: 6268
% 2.55/0.71  % (32031)Time elapsed: 0.310 s
% 2.55/0.71  % (32031)------------------------------
% 2.55/0.71  % (32031)------------------------------
% 2.55/0.71  % (32060)Refutation not found, incomplete strategy% (32060)------------------------------
% 2.55/0.71  % (32060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.71  % (32060)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.71  
% 2.55/0.71  % (32060)Memory used [KB]: 6140
% 2.55/0.71  % (32060)Time elapsed: 0.128 s
% 2.55/0.71  % (32060)------------------------------
% 2.55/0.71  % (32060)------------------------------
% 2.55/0.73  % (32059)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.34/0.80  % (32052)Time limit reached!
% 3.34/0.80  % (32052)------------------------------
% 3.34/0.80  % (32052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.80  % (32052)Termination reason: Time limit
% 3.34/0.80  % (32052)Termination phase: Saturation
% 3.34/0.80  
% 3.34/0.80  % (32052)Memory used [KB]: 12409
% 3.34/0.80  % (32052)Time elapsed: 0.400 s
% 3.34/0.80  % (32052)------------------------------
% 3.34/0.80  % (32052)------------------------------
% 3.34/0.82  % (32030)Time limit reached!
% 3.34/0.82  % (32030)------------------------------
% 3.34/0.82  % (32030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.82  % (32030)Termination reason: Time limit
% 3.34/0.82  
% 3.34/0.82  % (32030)Memory used [KB]: 6524
% 3.34/0.82  % (32030)Time elapsed: 0.421 s
% 3.34/0.82  % (32030)------------------------------
% 3.34/0.82  % (32030)------------------------------
% 3.57/0.86  % (32062)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.57/0.88  % (32061)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.57/0.90  % (32058)Refutation found. Thanks to Tanya!
% 3.57/0.90  % SZS status Theorem for theBenchmark
% 3.57/0.90  % SZS output start Proof for theBenchmark
% 3.57/0.90  fof(f2745,plain,(
% 3.57/0.90    $false),
% 3.57/0.90    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f120,f126,f132,f141,f142,f146,f150,f154,f158,f162,f166,f170,f181,f185,f194,f203,f207,f218,f222,f229,f248,f261,f266,f270,f274,f301,f319,f330,f341,f349,f362,f387,f431,f444,f483,f488,f498,f544,f575,f590,f654,f715,f825,f1114,f1500,f1854,f1972,f2194,f2322,f2333,f2403,f2441,f2600,f2605,f2676,f2689,f2696,f2716,f2744])).
% 3.57/0.90  fof(f2744,plain,(
% 3.57/0.90    ~spl4_130 | spl4_197 | ~spl4_204),
% 3.57/0.90    inference(avatar_contradiction_clause,[],[f2743])).
% 3.57/0.90  fof(f2743,plain,(
% 3.57/0.90    $false | (~spl4_130 | spl4_197 | ~spl4_204)),
% 3.57/0.90    inference(subsumption_resolution,[],[f2599,f2720])).
% 3.57/0.90  fof(f2720,plain,(
% 3.57/0.90    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (~spl4_130 | ~spl4_204)),
% 3.57/0.90    inference(superposition,[],[f1499,f2688])).
% 3.57/0.90  fof(f2688,plain,(
% 3.57/0.90    sK3 = k1_tops_1(sK1,sK3) | ~spl4_204),
% 3.57/0.90    inference(avatar_component_clause,[],[f2686])).
% 3.57/0.90  fof(f2686,plain,(
% 3.57/0.90    spl4_204 <=> sK3 = k1_tops_1(sK1,sK3)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_204])])).
% 3.57/0.90  fof(f1499,plain,(
% 3.57/0.90    r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~spl4_130),
% 3.57/0.90    inference(avatar_component_clause,[],[f1497])).
% 3.57/0.90  fof(f1497,plain,(
% 3.57/0.90    spl4_130 <=> r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).
% 3.57/0.90  fof(f2599,plain,(
% 3.57/0.90    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | spl4_197),
% 3.57/0.90    inference(avatar_component_clause,[],[f2597])).
% 3.57/0.90  fof(f2597,plain,(
% 3.57/0.90    spl4_197 <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).
% 3.57/0.90  fof(f2716,plain,(
% 3.57/0.90    ~spl4_13 | spl4_202),
% 3.57/0.90    inference(avatar_contradiction_clause,[],[f2711])).
% 3.57/0.90  fof(f2711,plain,(
% 3.57/0.90    $false | (~spl4_13 | spl4_202)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f149,f2680])).
% 3.57/0.90  fof(f2680,plain,(
% 3.57/0.90    ~r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) | spl4_202),
% 3.57/0.90    inference(avatar_component_clause,[],[f2678])).
% 3.57/0.90  fof(f2678,plain,(
% 3.57/0.90    spl4_202 <=> r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).
% 3.57/0.90  fof(f149,plain,(
% 3.57/0.90    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl4_13),
% 3.57/0.90    inference(avatar_component_clause,[],[f148])).
% 3.57/0.90  fof(f148,plain,(
% 3.57/0.90    spl4_13 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 3.57/0.90  fof(f2696,plain,(
% 3.57/0.90    ~spl4_3 | ~spl4_6 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_59 | ~spl4_60 | ~spl4_62 | spl4_203),
% 3.57/0.90    inference(avatar_contradiction_clause,[],[f2695])).
% 3.57/0.90  fof(f2695,plain,(
% 3.57/0.90    $false | (~spl4_3 | ~spl4_6 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_59 | ~spl4_60 | ~spl4_62 | spl4_203)),
% 3.57/0.90    inference(subsumption_resolution,[],[f115,f2694])).
% 3.57/0.90  fof(f2694,plain,(
% 3.57/0.90    ~v3_pre_topc(sK3,sK1) | (~spl4_3 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_59 | ~spl4_60 | ~spl4_62 | spl4_203)),
% 3.57/0.90    inference(forward_demodulation,[],[f2693,f589])).
% 3.57/0.90  fof(f589,plain,(
% 3.57/0.90    sK3 = k3_xboole_0(sK3,u1_struct_0(sK1)) | ~spl4_62),
% 3.57/0.90    inference(avatar_component_clause,[],[f587])).
% 3.57/0.90  fof(f587,plain,(
% 3.57/0.90    spl4_62 <=> sK3 = k3_xboole_0(sK3,u1_struct_0(sK1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 3.57/0.90  fof(f2693,plain,(
% 3.57/0.90    ~v3_pre_topc(k3_xboole_0(sK3,u1_struct_0(sK1)),sK1) | (~spl4_3 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_59 | ~spl4_60 | spl4_203)),
% 3.57/0.90    inference(forward_demodulation,[],[f2692,f578])).
% 3.57/0.90  fof(f578,plain,(
% 3.57/0.90    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl4_17 | ~spl4_60)),
% 3.57/0.90    inference(superposition,[],[f574,f165])).
% 3.57/0.90  fof(f165,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl4_17),
% 3.57/0.90    inference(avatar_component_clause,[],[f164])).
% 3.57/0.90  fof(f164,plain,(
% 3.57/0.90    spl4_17 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 3.57/0.90  fof(f574,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl4_60),
% 3.57/0.90    inference(avatar_component_clause,[],[f573])).
% 3.57/0.90  fof(f573,plain,(
% 3.57/0.90    spl4_60 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 3.57/0.90  fof(f2692,plain,(
% 3.57/0.90    ~v3_pre_topc(k3_xboole_0(u1_struct_0(sK1),sK3),sK1) | (~spl4_3 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_59 | spl4_203)),
% 3.57/0.90    inference(forward_demodulation,[],[f2691,f571])).
% 3.57/0.90  fof(f571,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | (~spl4_19 | ~spl4_22 | ~spl4_59)),
% 3.57/0.90    inference(forward_demodulation,[],[f545,f180])).
% 3.57/0.90  fof(f180,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_19),
% 3.57/0.90    inference(avatar_component_clause,[],[f179])).
% 3.57/0.90  fof(f179,plain,(
% 3.57/0.90    spl4_19 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 3.57/0.90  fof(f545,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | (~spl4_22 | ~spl4_59)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f543,f202])).
% 3.57/0.90  fof(f202,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_22),
% 3.57/0.90    inference(avatar_component_clause,[],[f201])).
% 3.57/0.90  fof(f201,plain,(
% 3.57/0.90    spl4_22 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 3.57/0.90  fof(f543,plain,(
% 3.57/0.90    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl4_59),
% 3.57/0.90    inference(avatar_component_clause,[],[f542])).
% 3.57/0.90  fof(f542,plain,(
% 3.57/0.90    spl4_59 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 3.57/0.90  fof(f2691,plain,(
% 3.57/0.90    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3)),sK1) | (~spl4_3 | ~spl4_28 | ~spl4_59 | spl4_203)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f100,f543,f2684,f247])).
% 3.57/0.90  fof(f247,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_28),
% 3.57/0.90    inference(avatar_component_clause,[],[f246])).
% 3.57/0.90  fof(f246,plain,(
% 3.57/0.90    spl4_28 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 3.57/0.90  fof(f2684,plain,(
% 3.57/0.90    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | spl4_203),
% 3.57/0.90    inference(avatar_component_clause,[],[f2682])).
% 3.57/0.90  fof(f2682,plain,(
% 3.57/0.90    spl4_203 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_203])])).
% 3.57/0.90  fof(f100,plain,(
% 3.57/0.90    l1_pre_topc(sK1) | ~spl4_3),
% 3.57/0.90    inference(avatar_component_clause,[],[f98])).
% 3.57/0.90  fof(f98,plain,(
% 3.57/0.90    spl4_3 <=> l1_pre_topc(sK1)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 3.57/0.90  fof(f115,plain,(
% 3.57/0.90    v3_pre_topc(sK3,sK1) | ~spl4_6),
% 3.57/0.90    inference(avatar_component_clause,[],[f113])).
% 3.57/0.90  fof(f113,plain,(
% 3.57/0.90    spl4_6 <=> v3_pre_topc(sK3,sK1)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 3.57/0.90  fof(f2689,plain,(
% 3.57/0.90    ~spl4_202 | ~spl4_3 | ~spl4_203 | spl4_204 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_54 | ~spl4_59 | ~spl4_60 | ~spl4_62 | ~spl4_68),
% 3.57/0.90    inference(avatar_split_clause,[],[f694,f652,f587,f573,f542,f485,f201,f179,f164,f2686,f2682,f98,f2678])).
% 3.57/0.90  fof(f485,plain,(
% 3.57/0.90    spl4_54 <=> k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 3.57/0.90  fof(f652,plain,(
% 3.57/0.90    spl4_68 <=> ! [X3,X2] : (~v4_pre_topc(X2,X3) | k2_pre_topc(X3,X2) = X2 | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X3)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 3.57/0.90  fof(f694,plain,(
% 3.57/0.90    sK3 = k1_tops_1(sK1,sK3) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | ~l1_pre_topc(sK1) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) | (~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_54 | ~spl4_59 | ~spl4_60 | ~spl4_62 | ~spl4_68)),
% 3.57/0.90    inference(forward_demodulation,[],[f693,f589])).
% 3.57/0.90  fof(f693,plain,(
% 3.57/0.90    k1_tops_1(sK1,sK3) = k3_xboole_0(sK3,u1_struct_0(sK1)) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | ~l1_pre_topc(sK1) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) | (~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_54 | ~spl4_59 | ~spl4_60 | ~spl4_68)),
% 3.57/0.90    inference(forward_demodulation,[],[f692,f578])).
% 3.57/0.90  fof(f692,plain,(
% 3.57/0.90    k1_tops_1(sK1,sK3) = k3_xboole_0(u1_struct_0(sK1),sK3) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | ~l1_pre_topc(sK1) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) | (~spl4_19 | ~spl4_22 | ~spl4_54 | ~spl4_59 | ~spl4_68)),
% 3.57/0.90    inference(forward_demodulation,[],[f676,f571])).
% 3.57/0.90  fof(f676,plain,(
% 3.57/0.90    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3)) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | ~l1_pre_topc(sK1) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) | (~spl4_54 | ~spl4_68)),
% 3.57/0.90    inference(superposition,[],[f487,f653])).
% 3.57/0.90  fof(f653,plain,(
% 3.57/0.90    ( ! [X2,X3] : (k2_pre_topc(X3,X2) = X2 | ~v4_pre_topc(X2,X3) | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X3))) ) | ~spl4_68),
% 3.57/0.90    inference(avatar_component_clause,[],[f652])).
% 3.57/0.90  fof(f487,plain,(
% 3.57/0.90    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))) | ~spl4_54),
% 3.57/0.90    inference(avatar_component_clause,[],[f485])).
% 3.57/0.90  fof(f2676,plain,(
% 3.57/0.90    ~spl4_2 | ~spl4_4 | spl4_11 | ~spl4_166 | ~spl4_38 | ~spl4_37 | ~spl4_47 | ~spl4_193),
% 3.57/0.90    inference(avatar_split_clause,[],[f2430,f2319,f428,f328,f338,f1963,f138,f103,f93])).
% 3.57/0.90  fof(f93,plain,(
% 3.57/0.90    spl4_2 <=> l1_pre_topc(sK0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.57/0.90  fof(f103,plain,(
% 3.57/0.90    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 3.57/0.90  fof(f138,plain,(
% 3.57/0.90    spl4_11 <=> v4_tops_1(sK2,sK0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 3.57/0.90  fof(f1963,plain,(
% 3.57/0.90    spl4_166 <=> r1_tarski(sK2,sK2)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).
% 3.57/0.90  fof(f338,plain,(
% 3.57/0.90    spl4_38 <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 3.57/0.90  fof(f328,plain,(
% 3.57/0.90    spl4_37 <=> ! [X1,X0] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 3.57/0.90  fof(f428,plain,(
% 3.57/0.90    spl4_47 <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 3.57/0.90  fof(f2319,plain,(
% 3.57/0.90    spl4_193 <=> sK2 = k1_tops_1(sK0,sK2)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_193])])).
% 3.57/0.90  fof(f2430,plain,(
% 3.57/0.90    ~r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~r1_tarski(sK2,sK2) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_37 | ~spl4_47 | ~spl4_193)),
% 3.57/0.90    inference(forward_demodulation,[],[f433,f2321])).
% 3.57/0.90  fof(f2321,plain,(
% 3.57/0.90    sK2 = k1_tops_1(sK0,sK2) | ~spl4_193),
% 3.57/0.90    inference(avatar_component_clause,[],[f2319])).
% 3.57/0.90  fof(f433,plain,(
% 3.57/0.90    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_37 | ~spl4_47)),
% 3.57/0.90    inference(superposition,[],[f329,f430])).
% 3.57/0.90  fof(f430,plain,(
% 3.57/0.90    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~spl4_47),
% 3.57/0.90    inference(avatar_component_clause,[],[f428])).
% 3.57/0.90  fof(f329,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_37),
% 3.57/0.90    inference(avatar_component_clause,[],[f328])).
% 3.57/0.90  fof(f2605,plain,(
% 3.57/0.90    ~spl4_2 | ~spl4_4 | spl4_7 | ~spl4_32 | ~spl4_47),
% 3.57/0.90    inference(avatar_split_clause,[],[f2360,f428,f268,f117,f103,f93])).
% 3.57/0.90  fof(f117,plain,(
% 3.57/0.90    spl4_7 <=> v6_tops_1(sK2,sK0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 3.57/0.90  fof(f268,plain,(
% 3.57/0.90    spl4_32 <=> ! [X1,X0] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 3.57/0.90  fof(f2360,plain,(
% 3.57/0.90    v6_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_32 | ~spl4_47)),
% 3.57/0.90    inference(trivial_inequality_removal,[],[f2204])).
% 3.57/0.90  fof(f2204,plain,(
% 3.57/0.90    sK2 != sK2 | v6_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_32 | ~spl4_47)),
% 3.57/0.90    inference(superposition,[],[f269,f430])).
% 3.57/0.90  fof(f269,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_32),
% 3.57/0.90    inference(avatar_component_clause,[],[f268])).
% 3.57/0.90  fof(f2600,plain,(
% 3.57/0.90    ~spl4_197 | ~spl4_3 | ~spl4_5 | ~spl4_8 | spl4_48 | ~spl4_77),
% 3.57/0.90    inference(avatar_split_clause,[],[f2145,f823,f441,f123,f108,f98,f2597])).
% 3.57/0.90  fof(f108,plain,(
% 3.57/0.90    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 3.57/0.90  fof(f123,plain,(
% 3.57/0.90    spl4_8 <=> v4_tops_1(sK3,sK1)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 3.57/0.90  fof(f441,plain,(
% 3.57/0.90    spl4_48 <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 3.57/0.90  fof(f823,plain,(
% 3.57/0.90    spl4_77 <=> ! [X1,X0] : (~v4_tops_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 | ~r1_tarski(X0,k1_tops_1(X1,k2_pre_topc(X1,X0))))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 3.57/0.90  fof(f2145,plain,(
% 3.57/0.90    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (~spl4_3 | ~spl4_5 | ~spl4_8 | spl4_48 | ~spl4_77)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f100,f110,f443,f125,f824])).
% 3.57/0.90  fof(f824,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(X1,k2_pre_topc(X1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 | ~v4_tops_1(X0,X1)) ) | ~spl4_77),
% 3.57/0.90    inference(avatar_component_clause,[],[f823])).
% 3.57/0.90  fof(f125,plain,(
% 3.57/0.90    v4_tops_1(sK3,sK1) | ~spl4_8),
% 3.57/0.90    inference(avatar_component_clause,[],[f123])).
% 3.57/0.90  fof(f443,plain,(
% 3.57/0.90    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | spl4_48),
% 3.57/0.90    inference(avatar_component_clause,[],[f441])).
% 3.57/0.90  fof(f110,plain,(
% 3.57/0.90    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_5),
% 3.57/0.90    inference(avatar_component_clause,[],[f108])).
% 3.57/0.90  fof(f2441,plain,(
% 3.57/0.90    ~spl4_2 | spl4_8 | ~spl4_11 | ~spl4_22 | ~spl4_35 | ~spl4_41 | ~spl4_159 | ~spl4_183),
% 3.57/0.90    inference(avatar_contradiction_clause,[],[f2439])).
% 3.57/0.90  fof(f2439,plain,(
% 3.57/0.90    $false | (~spl4_2 | spl4_8 | ~spl4_11 | ~spl4_22 | ~spl4_35 | ~spl4_41 | ~spl4_159 | ~spl4_183)),
% 3.57/0.90    inference(subsumption_resolution,[],[f2195,f2438])).
% 3.57/0.90  fof(f2438,plain,(
% 3.57/0.90    ~v3_pre_topc(sK2,sK0) | (spl4_8 | ~spl4_11)),
% 3.57/0.90    inference(subsumption_resolution,[],[f127,f139])).
% 3.57/0.90  fof(f139,plain,(
% 3.57/0.90    v4_tops_1(sK2,sK0) | ~spl4_11),
% 3.57/0.90    inference(avatar_component_clause,[],[f138])).
% 3.57/0.90  fof(f127,plain,(
% 3.57/0.90    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | spl4_8),
% 3.57/0.90    inference(subsumption_resolution,[],[f58,f124])).
% 3.57/0.90  fof(f124,plain,(
% 3.57/0.90    ~v4_tops_1(sK3,sK1) | spl4_8),
% 3.57/0.90    inference(avatar_component_clause,[],[f123])).
% 3.57/0.90  fof(f58,plain,(
% 3.57/0.90    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f41,plain,(
% 3.57/0.90    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.57/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f40,f39,f38,f37])).
% 3.57/0.90  fof(f37,plain,(
% 3.57/0.90    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.57/0.90    introduced(choice_axiom,[])).
% 3.57/0.90  fof(f38,plain,(
% 3.57/0.90    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 3.57/0.90    introduced(choice_axiom,[])).
% 3.57/0.90  fof(f39,plain,(
% 3.57/0.90    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.57/0.90    introduced(choice_axiom,[])).
% 3.57/0.90  fof(f40,plain,(
% 3.57/0.90    ? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.57/0.90    introduced(choice_axiom,[])).
% 3.57/0.90  fof(f21,plain,(
% 3.57/0.90    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.57/0.90    inference(flattening,[],[f20])).
% 3.57/0.90  fof(f20,plain,(
% 3.57/0.90    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.57/0.90    inference(ennf_transformation,[],[f19])).
% 3.57/0.90  fof(f19,negated_conjecture,(
% 3.57/0.90    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 3.57/0.90    inference(negated_conjecture,[],[f18])).
% 3.57/0.90  fof(f18,conjecture,(
% 3.57/0.90    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).
% 3.57/0.90  fof(f2195,plain,(
% 3.57/0.90    v3_pre_topc(sK2,sK0) | (~spl4_2 | ~spl4_22 | ~spl4_35 | ~spl4_41 | ~spl4_159 | ~spl4_183)),
% 3.57/0.90    inference(forward_demodulation,[],[f2193,f2133])).
% 3.57/0.90  fof(f2133,plain,(
% 3.57/0.90    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | (~spl4_2 | ~spl4_22 | ~spl4_35 | ~spl4_41 | ~spl4_159)),
% 3.57/0.90    inference(forward_demodulation,[],[f377,f1853])).
% 3.57/0.90  fof(f1853,plain,(
% 3.57/0.90    sK2 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)))) | ~spl4_159),
% 3.57/0.90    inference(avatar_component_clause,[],[f1851])).
% 3.57/0.90  fof(f1851,plain,(
% 3.57/0.90    spl4_159 <=> sK2 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_159])])).
% 3.57/0.90  fof(f377,plain,(
% 3.57/0.90    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)))) | (~spl4_2 | ~spl4_22 | ~spl4_35 | ~spl4_41)),
% 3.57/0.90    inference(forward_demodulation,[],[f366,f370])).
% 3.57/0.90  fof(f370,plain,(
% 3.57/0.90    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)) | (~spl4_22 | ~spl4_41)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f361,f202])).
% 3.57/0.90  fof(f361,plain,(
% 3.57/0.90    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_41),
% 3.57/0.90    inference(avatar_component_clause,[],[f359])).
% 3.57/0.90  fof(f359,plain,(
% 3.57/0.90    spl4_41 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 3.57/0.90  fof(f366,plain,(
% 3.57/0.90    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)))) | (~spl4_2 | ~spl4_35 | ~spl4_41)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f95,f361,f300])).
% 3.57/0.90  fof(f300,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_35),
% 3.57/0.90    inference(avatar_component_clause,[],[f299])).
% 3.57/0.90  fof(f299,plain,(
% 3.57/0.90    spl4_35 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 3.57/0.90  fof(f95,plain,(
% 3.57/0.90    l1_pre_topc(sK0) | ~spl4_2),
% 3.57/0.90    inference(avatar_component_clause,[],[f93])).
% 3.57/0.90  fof(f2193,plain,(
% 3.57/0.90    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | ~spl4_183),
% 3.57/0.90    inference(avatar_component_clause,[],[f2191])).
% 3.57/0.90  fof(f2191,plain,(
% 3.57/0.90    spl4_183 <=> v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_183])])).
% 3.57/0.90  fof(f2403,plain,(
% 3.57/0.90    ~spl4_13 | spl4_191),
% 3.57/0.90    inference(avatar_contradiction_clause,[],[f2398])).
% 3.57/0.90  fof(f2398,plain,(
% 3.57/0.90    $false | (~spl4_13 | spl4_191)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f149,f2313])).
% 3.57/0.90  fof(f2313,plain,(
% 3.57/0.90    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | spl4_191),
% 3.57/0.90    inference(avatar_component_clause,[],[f2311])).
% 3.57/0.90  fof(f2311,plain,(
% 3.57/0.90    spl4_191 <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_191])])).
% 3.57/0.90  fof(f2333,plain,(
% 3.57/0.90    ~spl4_2 | ~spl4_10 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_53 | ~spl4_59 | ~spl4_60 | spl4_192),
% 3.57/0.90    inference(avatar_contradiction_clause,[],[f2332])).
% 3.57/0.90  fof(f2332,plain,(
% 3.57/0.90    $false | (~spl4_2 | ~spl4_10 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_53 | ~spl4_59 | ~spl4_60 | spl4_192)),
% 3.57/0.90    inference(subsumption_resolution,[],[f135,f2331])).
% 3.57/0.90  fof(f2331,plain,(
% 3.57/0.90    ~v3_pre_topc(sK2,sK0) | (~spl4_2 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_53 | ~spl4_59 | ~spl4_60 | spl4_192)),
% 3.57/0.90    inference(forward_demodulation,[],[f2330,f482])).
% 3.57/0.90  fof(f482,plain,(
% 3.57/0.90    sK2 = k3_xboole_0(sK2,u1_struct_0(sK0)) | ~spl4_53),
% 3.57/0.90    inference(avatar_component_clause,[],[f480])).
% 3.57/0.90  fof(f480,plain,(
% 3.57/0.90    spl4_53 <=> sK2 = k3_xboole_0(sK2,u1_struct_0(sK0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 3.57/0.90  fof(f2330,plain,(
% 3.57/0.90    ~v3_pre_topc(k3_xboole_0(sK2,u1_struct_0(sK0)),sK0) | (~spl4_2 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_59 | ~spl4_60 | spl4_192)),
% 3.57/0.90    inference(forward_demodulation,[],[f2329,f578])).
% 3.57/0.90  fof(f2329,plain,(
% 3.57/0.90    ~v3_pre_topc(k3_xboole_0(u1_struct_0(sK0),sK2),sK0) | (~spl4_2 | ~spl4_19 | ~spl4_22 | ~spl4_28 | ~spl4_59 | spl4_192)),
% 3.57/0.90    inference(forward_demodulation,[],[f2328,f571])).
% 3.57/0.90  fof(f2328,plain,(
% 3.57/0.90    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),sK0) | (~spl4_2 | ~spl4_28 | ~spl4_59 | spl4_192)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f95,f543,f2317,f247])).
% 3.57/0.90  fof(f2317,plain,(
% 3.57/0.90    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | spl4_192),
% 3.57/0.90    inference(avatar_component_clause,[],[f2315])).
% 3.57/0.90  fof(f2315,plain,(
% 3.57/0.90    spl4_192 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).
% 3.57/0.90  fof(f135,plain,(
% 3.57/0.90    v3_pre_topc(sK2,sK0) | ~spl4_10),
% 3.57/0.90    inference(avatar_component_clause,[],[f134])).
% 3.57/0.90  fof(f134,plain,(
% 3.57/0.90    spl4_10 <=> v3_pre_topc(sK2,sK0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.57/0.90  fof(f2322,plain,(
% 3.57/0.90    ~spl4_191 | ~spl4_2 | ~spl4_192 | spl4_193 | ~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_53 | ~spl4_55 | ~spl4_59 | ~spl4_60 | ~spl4_68),
% 3.57/0.90    inference(avatar_split_clause,[],[f691,f652,f573,f542,f495,f480,f201,f179,f164,f2319,f2315,f93,f2311])).
% 3.57/0.90  fof(f495,plain,(
% 3.57/0.90    spl4_55 <=> k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 3.57/0.90  fof(f691,plain,(
% 3.57/0.90    sK2 = k1_tops_1(sK0,sK2) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | (~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_53 | ~spl4_55 | ~spl4_59 | ~spl4_60 | ~spl4_68)),
% 3.57/0.90    inference(forward_demodulation,[],[f690,f482])).
% 3.57/0.90  fof(f690,plain,(
% 3.57/0.90    k3_xboole_0(sK2,u1_struct_0(sK0)) = k1_tops_1(sK0,sK2) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | (~spl4_17 | ~spl4_19 | ~spl4_22 | ~spl4_55 | ~spl4_59 | ~spl4_60 | ~spl4_68)),
% 3.57/0.90    inference(forward_demodulation,[],[f689,f578])).
% 3.57/0.90  fof(f689,plain,(
% 3.57/0.90    k1_tops_1(sK0,sK2) = k3_xboole_0(u1_struct_0(sK0),sK2) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | (~spl4_19 | ~spl4_22 | ~spl4_55 | ~spl4_59 | ~spl4_68)),
% 3.57/0.90    inference(forward_demodulation,[],[f671,f571])).
% 3.57/0.90  fof(f671,plain,(
% 3.57/0.90    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | (~spl4_55 | ~spl4_68)),
% 3.57/0.90    inference(superposition,[],[f497,f653])).
% 3.57/0.90  fof(f497,plain,(
% 3.57/0.90    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))) | ~spl4_55),
% 3.57/0.90    inference(avatar_component_clause,[],[f495])).
% 3.57/0.90  fof(f2194,plain,(
% 3.57/0.90    spl4_183 | ~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_70),
% 3.57/0.90    inference(avatar_split_clause,[],[f716,f713,f103,f93,f88,f2191])).
% 3.57/0.90  fof(f88,plain,(
% 3.57/0.90    spl4_1 <=> v2_pre_topc(sK0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.57/0.90  fof(f713,plain,(
% 3.57/0.90    spl4_70 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X0)),X1) | ~v2_pre_topc(X1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 3.57/0.90  fof(f716,plain,(
% 3.57/0.90    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_70)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f90,f95,f105,f714])).
% 3.57/0.90  fof(f714,plain,(
% 3.57/0.90    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X0)),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1)) ) | ~spl4_70),
% 3.57/0.90    inference(avatar_component_clause,[],[f713])).
% 3.57/0.90  fof(f105,plain,(
% 3.57/0.90    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 3.57/0.90    inference(avatar_component_clause,[],[f103])).
% 3.57/0.90  fof(f90,plain,(
% 3.57/0.90    v2_pre_topc(sK0) | ~spl4_1),
% 3.57/0.90    inference(avatar_component_clause,[],[f88])).
% 3.57/0.90  fof(f1972,plain,(
% 3.57/0.90    ~spl4_12 | spl4_166),
% 3.57/0.90    inference(avatar_contradiction_clause,[],[f1967])).
% 3.57/0.90  fof(f1967,plain,(
% 3.57/0.90    $false | (~spl4_12 | spl4_166)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f145,f1965])).
% 3.57/0.90  fof(f1965,plain,(
% 3.57/0.90    ~r1_tarski(sK2,sK2) | spl4_166),
% 3.57/0.90    inference(avatar_component_clause,[],[f1963])).
% 3.57/0.90  fof(f145,plain,(
% 3.57/0.90    ( ! [X1] : (r1_tarski(X1,X1)) ) | ~spl4_12),
% 3.57/0.90    inference(avatar_component_clause,[],[f144])).
% 3.57/0.90  fof(f144,plain,(
% 3.57/0.90    spl4_12 <=> ! [X1] : r1_tarski(X1,X1)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 3.57/0.90  fof(f1854,plain,(
% 3.57/0.90    spl4_159 | ~spl4_2 | ~spl4_4 | ~spl4_7 | ~spl4_22 | ~spl4_30 | ~spl4_35 | ~spl4_41),
% 3.57/0.90    inference(avatar_split_clause,[],[f378,f359,f299,f259,f201,f117,f103,f93,f1851])).
% 3.57/0.90  fof(f259,plain,(
% 3.57/0.90    spl4_30 <=> ! [X1,X0] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 3.57/0.90  fof(f378,plain,(
% 3.57/0.90    sK2 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)))) | (~spl4_2 | ~spl4_4 | ~spl4_7 | ~spl4_22 | ~spl4_30 | ~spl4_35 | ~spl4_41)),
% 3.57/0.90    inference(forward_demodulation,[],[f377,f285])).
% 3.57/0.90  fof(f285,plain,(
% 3.57/0.90    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | (~spl4_2 | ~spl4_4 | ~spl4_7 | ~spl4_30)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f95,f119,f105,f260])).
% 3.57/0.90  fof(f260,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_30),
% 3.57/0.90    inference(avatar_component_clause,[],[f259])).
% 3.57/0.90  fof(f119,plain,(
% 3.57/0.90    v6_tops_1(sK2,sK0) | ~spl4_7),
% 3.57/0.90    inference(avatar_component_clause,[],[f117])).
% 3.57/0.90  fof(f1500,plain,(
% 3.57/0.90    spl4_130 | ~spl4_3 | ~spl4_5 | ~spl4_36 | ~spl4_39 | ~spl4_42),
% 3.57/0.90    inference(avatar_split_clause,[],[f392,f384,f346,f317,f108,f98,f1497])).
% 3.57/0.90  fof(f317,plain,(
% 3.57/0.90    spl4_36 <=> ! [X1,X0,X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 3.57/0.90  fof(f346,plain,(
% 3.57/0.90    spl4_39 <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 3.57/0.90  fof(f384,plain,(
% 3.57/0.90    spl4_42 <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 3.57/0.90  fof(f392,plain,(
% 3.57/0.90    r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (~spl4_3 | ~spl4_5 | ~spl4_36 | ~spl4_39 | ~spl4_42)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f100,f110,f348,f386,f318])).
% 3.57/0.90  fof(f318,plain,(
% 3.57/0.90    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_36),
% 3.57/0.90    inference(avatar_component_clause,[],[f317])).
% 3.57/0.90  fof(f386,plain,(
% 3.57/0.90    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_42),
% 3.57/0.90    inference(avatar_component_clause,[],[f384])).
% 3.57/0.90  fof(f348,plain,(
% 3.57/0.90    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~spl4_39),
% 3.57/0.90    inference(avatar_component_clause,[],[f346])).
% 3.57/0.90  fof(f1114,plain,(
% 3.57/0.90    spl4_10 | ~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_7 | ~spl4_24 | ~spl4_30 | ~spl4_41),
% 3.57/0.90    inference(avatar_split_clause,[],[f379,f359,f259,f216,f117,f103,f93,f88,f134])).
% 3.57/0.90  fof(f216,plain,(
% 3.57/0.90    spl4_24 <=> ! [X1,X0] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 3.57/0.90  fof(f379,plain,(
% 3.57/0.90    v3_pre_topc(sK2,sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_7 | ~spl4_24 | ~spl4_30 | ~spl4_41)),
% 3.57/0.90    inference(forward_demodulation,[],[f364,f285])).
% 3.57/0.90  fof(f364,plain,(
% 3.57/0.90    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | (~spl4_1 | ~spl4_2 | ~spl4_24 | ~spl4_41)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f90,f95,f361,f217])).
% 3.57/0.90  fof(f217,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_24),
% 3.57/0.90    inference(avatar_component_clause,[],[f216])).
% 3.57/0.90  fof(f825,plain,(
% 3.57/0.90    spl4_77 | ~spl4_20 | ~spl4_33),
% 3.57/0.90    inference(avatar_split_clause,[],[f292,f272,f183,f823])).
% 3.57/0.90  fof(f183,plain,(
% 3.57/0.90    spl4_20 <=> ! [X1,X0] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 3.57/0.90  fof(f272,plain,(
% 3.57/0.90    spl4_33 <=> ! [X1,X0] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 3.57/0.90  fof(f292,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~v4_tops_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 | ~r1_tarski(X0,k1_tops_1(X1,k2_pre_topc(X1,X0)))) ) | (~spl4_20 | ~spl4_33)),
% 3.57/0.90    inference(resolution,[],[f273,f184])).
% 3.57/0.90  fof(f184,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) ) | ~spl4_20),
% 3.57/0.90    inference(avatar_component_clause,[],[f183])).
% 3.57/0.90  fof(f273,plain,(
% 3.57/0.90    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_33),
% 3.57/0.90    inference(avatar_component_clause,[],[f272])).
% 3.57/0.90  fof(f715,plain,(
% 3.57/0.90    spl4_70 | ~spl4_24 | ~spl4_25),
% 3.57/0.90    inference(avatar_split_clause,[],[f240,f220,f216,f713])).
% 3.57/0.90  fof(f220,plain,(
% 3.57/0.90    spl4_25 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 3.57/0.90  fof(f240,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X0)),X1) | ~v2_pre_topc(X1)) ) | (~spl4_24 | ~spl4_25)),
% 3.57/0.90    inference(duplicate_literal_removal,[],[f236])).
% 3.57/0.90  fof(f236,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X0)),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl4_24 | ~spl4_25)),
% 3.57/0.90    inference(resolution,[],[f221,f217])).
% 3.57/0.90  fof(f221,plain,(
% 3.57/0.90    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_25),
% 3.57/0.90    inference(avatar_component_clause,[],[f220])).
% 3.57/0.90  fof(f654,plain,(
% 3.57/0.90    spl4_68 | ~spl4_16 | ~spl4_26),
% 3.57/0.90    inference(avatar_split_clause,[],[f252,f227,f160,f652])).
% 3.57/0.90  fof(f160,plain,(
% 3.57/0.90    spl4_16 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 3.57/0.90  fof(f227,plain,(
% 3.57/0.90    spl4_26 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 3.57/0.90  fof(f252,plain,(
% 3.57/0.90    ( ! [X2,X3] : (~v4_pre_topc(X2,X3) | k2_pre_topc(X3,X2) = X2 | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X3))) ) | (~spl4_16 | ~spl4_26)),
% 3.57/0.90    inference(resolution,[],[f228,f161])).
% 3.57/0.90  fof(f161,plain,(
% 3.57/0.90    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl4_16),
% 3.57/0.90    inference(avatar_component_clause,[],[f160])).
% 3.57/0.90  fof(f228,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) ) | ~spl4_26),
% 3.57/0.90    inference(avatar_component_clause,[],[f227])).
% 3.57/0.90  fof(f590,plain,(
% 3.57/0.90    spl4_62 | ~spl4_18 | ~spl4_31),
% 3.57/0.90    inference(avatar_split_clause,[],[f289,f263,f168,f587])).
% 3.57/0.90  fof(f168,plain,(
% 3.57/0.90    spl4_18 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 3.57/0.90  fof(f263,plain,(
% 3.57/0.90    spl4_31 <=> r1_tarski(sK3,u1_struct_0(sK1))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 3.57/0.90  fof(f289,plain,(
% 3.57/0.90    sK3 = k3_xboole_0(sK3,u1_struct_0(sK1)) | (~spl4_18 | ~spl4_31)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f265,f169])).
% 3.57/0.90  fof(f169,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl4_18),
% 3.57/0.90    inference(avatar_component_clause,[],[f168])).
% 3.57/0.90  fof(f265,plain,(
% 3.57/0.90    r1_tarski(sK3,u1_struct_0(sK1)) | ~spl4_31),
% 3.57/0.90    inference(avatar_component_clause,[],[f263])).
% 3.57/0.90  fof(f575,plain,(
% 3.57/0.90    spl4_60 | ~spl4_14 | ~spl4_17),
% 3.57/0.90    inference(avatar_split_clause,[],[f186,f164,f152,f573])).
% 3.57/0.90  fof(f152,plain,(
% 3.57/0.90    spl4_14 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.57/0.90  fof(f186,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl4_14 | ~spl4_17)),
% 3.57/0.90    inference(superposition,[],[f165,f153])).
% 3.57/0.90  fof(f153,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl4_14),
% 3.57/0.90    inference(avatar_component_clause,[],[f152])).
% 3.57/0.90  fof(f544,plain,(
% 3.57/0.90    spl4_59 | ~spl4_13 | ~spl4_16),
% 3.57/0.90    inference(avatar_split_clause,[],[f176,f160,f148,f542])).
% 3.57/0.90  fof(f176,plain,(
% 3.57/0.90    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl4_13 | ~spl4_16)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f149,f161])).
% 3.57/0.90  fof(f498,plain,(
% 3.57/0.90    spl4_55 | ~spl4_2 | ~spl4_4 | ~spl4_22 | ~spl4_35),
% 3.57/0.90    inference(avatar_split_clause,[],[f315,f299,f201,f103,f93,f495])).
% 3.57/0.90  fof(f315,plain,(
% 3.57/0.90    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))) | (~spl4_2 | ~spl4_4 | ~spl4_22 | ~spl4_35)),
% 3.57/0.90    inference(forward_demodulation,[],[f302,f208])).
% 3.57/0.90  fof(f208,plain,(
% 3.57/0.90    k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2) | (~spl4_4 | ~spl4_22)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f105,f202])).
% 3.57/0.90  fof(f302,plain,(
% 3.57/0.90    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) | (~spl4_2 | ~spl4_4 | ~spl4_35)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f95,f105,f300])).
% 3.57/0.90  fof(f488,plain,(
% 3.57/0.90    spl4_54 | ~spl4_3 | ~spl4_5 | ~spl4_22 | ~spl4_35),
% 3.57/0.90    inference(avatar_split_clause,[],[f314,f299,f201,f108,f98,f485])).
% 3.57/0.90  fof(f314,plain,(
% 3.57/0.90    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))) | (~spl4_3 | ~spl4_5 | ~spl4_22 | ~spl4_35)),
% 3.57/0.90    inference(forward_demodulation,[],[f303,f209])).
% 3.57/0.90  fof(f209,plain,(
% 3.57/0.90    k4_xboole_0(u1_struct_0(sK1),sK3) = k3_subset_1(u1_struct_0(sK1),sK3) | (~spl4_5 | ~spl4_22)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f110,f202])).
% 3.57/0.90  fof(f303,plain,(
% 3.57/0.90    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) | (~spl4_3 | ~spl4_5 | ~spl4_35)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f100,f110,f300])).
% 3.57/0.90  fof(f483,plain,(
% 3.57/0.90    spl4_53 | ~spl4_18 | ~spl4_21),
% 3.57/0.90    inference(avatar_split_clause,[],[f223,f191,f168,f480])).
% 3.57/0.90  fof(f191,plain,(
% 3.57/0.90    spl4_21 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 3.57/0.90  fof(f223,plain,(
% 3.57/0.90    sK2 = k3_xboole_0(sK2,u1_struct_0(sK0)) | (~spl4_18 | ~spl4_21)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f193,f169])).
% 3.57/0.90  fof(f193,plain,(
% 3.57/0.90    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl4_21),
% 3.57/0.90    inference(avatar_component_clause,[],[f191])).
% 3.57/0.90  fof(f444,plain,(
% 3.57/0.90    ~spl4_48 | ~spl4_3 | ~spl4_5 | spl4_9 | ~spl4_32),
% 3.57/0.90    inference(avatar_split_clause,[],[f286,f268,f129,f108,f98,f441])).
% 3.57/0.90  fof(f129,plain,(
% 3.57/0.90    spl4_9 <=> v6_tops_1(sK3,sK1)),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 3.57/0.90  fof(f286,plain,(
% 3.57/0.90    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | (~spl4_3 | ~spl4_5 | spl4_9 | ~spl4_32)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f100,f131,f110,f269])).
% 3.57/0.90  fof(f131,plain,(
% 3.57/0.90    ~v6_tops_1(sK3,sK1) | spl4_9),
% 3.57/0.90    inference(avatar_component_clause,[],[f129])).
% 3.57/0.90  fof(f431,plain,(
% 3.57/0.90    spl4_47 | ~spl4_2 | ~spl4_4 | ~spl4_7 | ~spl4_30),
% 3.57/0.90    inference(avatar_split_clause,[],[f285,f259,f117,f103,f93,f428])).
% 3.57/0.90  fof(f387,plain,(
% 3.57/0.90    spl4_42 | ~spl4_3 | ~spl4_5 | ~spl4_25),
% 3.57/0.90    inference(avatar_split_clause,[],[f235,f220,f108,f98,f384])).
% 3.57/0.90  fof(f235,plain,(
% 3.57/0.90    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl4_3 | ~spl4_5 | ~spl4_25)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f100,f110,f221])).
% 3.57/0.90  fof(f362,plain,(
% 3.57/0.90    spl4_41 | ~spl4_2 | ~spl4_4 | ~spl4_25),
% 3.57/0.90    inference(avatar_split_clause,[],[f234,f220,f103,f93,f359])).
% 3.57/0.90  fof(f234,plain,(
% 3.57/0.90    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_4 | ~spl4_25)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f95,f105,f221])).
% 3.57/0.90  fof(f349,plain,(
% 3.57/0.90    spl4_39 | ~spl4_3 | ~spl4_5 | ~spl4_23),
% 3.57/0.90    inference(avatar_split_clause,[],[f211,f205,f108,f98,f346])).
% 3.57/0.90  fof(f205,plain,(
% 3.57/0.90    spl4_23 <=> ! [X1,X0] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 3.57/0.90  fof(f211,plain,(
% 3.57/0.90    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | (~spl4_3 | ~spl4_5 | ~spl4_23)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f100,f110,f206])).
% 3.57/0.90  fof(f206,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) ) | ~spl4_23),
% 3.57/0.90    inference(avatar_component_clause,[],[f205])).
% 3.57/0.90  fof(f341,plain,(
% 3.57/0.90    spl4_38 | ~spl4_2 | ~spl4_4 | ~spl4_23),
% 3.57/0.90    inference(avatar_split_clause,[],[f210,f205,f103,f93,f338])).
% 3.57/0.90  fof(f210,plain,(
% 3.57/0.90    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | (~spl4_2 | ~spl4_4 | ~spl4_23)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f95,f105,f206])).
% 3.57/0.90  fof(f330,plain,(
% 3.57/0.90    spl4_37),
% 3.57/0.90    inference(avatar_split_clause,[],[f70,f328])).
% 3.57/0.90  fof(f70,plain,(
% 3.57/0.90    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f45])).
% 3.57/0.90  fof(f45,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(flattening,[],[f44])).
% 3.57/0.90  fof(f44,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(nnf_transformation,[],[f28])).
% 3.57/0.90  fof(f28,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(ennf_transformation,[],[f13])).
% 3.57/0.90  fof(f13,axiom,(
% 3.57/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 3.57/0.90  fof(f319,plain,(
% 3.57/0.90    spl4_36),
% 3.57/0.90    inference(avatar_split_clause,[],[f71,f317])).
% 3.57/0.90  fof(f71,plain,(
% 3.57/0.90    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f30])).
% 3.57/0.90  fof(f30,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(flattening,[],[f29])).
% 3.57/0.90  fof(f29,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(ennf_transformation,[],[f17])).
% 3.57/0.90  fof(f17,axiom,(
% 3.57/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 3.57/0.90  fof(f301,plain,(
% 3.57/0.90    spl4_35),
% 3.57/0.90    inference(avatar_split_clause,[],[f61,f299])).
% 3.57/0.90  fof(f61,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f23])).
% 3.57/0.90  fof(f23,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(ennf_transformation,[],[f12])).
% 3.57/0.90  fof(f12,axiom,(
% 3.57/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 3.57/0.90  fof(f274,plain,(
% 3.57/0.90    spl4_33),
% 3.57/0.90    inference(avatar_split_clause,[],[f68,f272])).
% 3.57/0.90  fof(f68,plain,(
% 3.57/0.90    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f45])).
% 3.57/0.90  fof(f270,plain,(
% 3.57/0.90    spl4_32),
% 3.57/0.90    inference(avatar_split_clause,[],[f67,f268])).
% 3.57/0.90  fof(f67,plain,(
% 3.57/0.90    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f43])).
% 3.57/0.90  fof(f43,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(nnf_transformation,[],[f27])).
% 3.57/0.90  fof(f27,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(ennf_transformation,[],[f14])).
% 3.57/0.90  fof(f14,axiom,(
% 3.57/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).
% 3.57/0.90  fof(f266,plain,(
% 3.57/0.90    spl4_31 | ~spl4_5 | ~spl4_15),
% 3.57/0.90    inference(avatar_split_clause,[],[f172,f156,f108,f263])).
% 3.57/0.90  fof(f156,plain,(
% 3.57/0.90    spl4_15 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.57/0.90    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 3.57/0.90  fof(f172,plain,(
% 3.57/0.90    r1_tarski(sK3,u1_struct_0(sK1)) | (~spl4_5 | ~spl4_15)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f110,f157])).
% 3.57/0.90  fof(f157,plain,(
% 3.57/0.90    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl4_15),
% 3.57/0.90    inference(avatar_component_clause,[],[f156])).
% 3.57/0.90  fof(f261,plain,(
% 3.57/0.90    spl4_30),
% 3.57/0.90    inference(avatar_split_clause,[],[f66,f259])).
% 3.57/0.90  fof(f66,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f43])).
% 3.57/0.90  fof(f248,plain,(
% 3.57/0.90    spl4_28),
% 3.57/0.90    inference(avatar_split_clause,[],[f65,f246])).
% 3.57/0.90  fof(f65,plain,(
% 3.57/0.90    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f42])).
% 3.57/0.90  fof(f42,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(nnf_transformation,[],[f26])).
% 3.57/0.90  fof(f26,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(ennf_transformation,[],[f16])).
% 3.57/0.90  fof(f16,axiom,(
% 3.57/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 3.57/0.90  fof(f229,plain,(
% 3.57/0.90    spl4_26),
% 3.57/0.90    inference(avatar_split_clause,[],[f62,f227])).
% 3.57/0.90  fof(f62,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f25])).
% 3.57/0.90  fof(f25,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(flattening,[],[f24])).
% 3.57/0.90  fof(f24,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(ennf_transformation,[],[f11])).
% 3.57/0.90  fof(f11,axiom,(
% 3.57/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 3.57/0.90  fof(f222,plain,(
% 3.57/0.90    spl4_25),
% 3.57/0.90    inference(avatar_split_clause,[],[f79,f220])).
% 3.57/0.90  fof(f79,plain,(
% 3.57/0.90    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f36])).
% 3.57/0.90  fof(f36,plain,(
% 3.57/0.90    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(flattening,[],[f35])).
% 3.57/0.90  fof(f35,plain,(
% 3.57/0.90    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.57/0.90    inference(ennf_transformation,[],[f9])).
% 3.57/0.90  fof(f9,axiom,(
% 3.57/0.90    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 3.57/0.90  fof(f218,plain,(
% 3.57/0.90    spl4_24),
% 3.57/0.90    inference(avatar_split_clause,[],[f78,f216])).
% 3.57/0.90  fof(f78,plain,(
% 3.57/0.90    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f34])).
% 3.57/0.90  fof(f34,plain,(
% 3.57/0.90    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/0.90    inference(flattening,[],[f33])).
% 3.57/0.90  fof(f33,plain,(
% 3.57/0.90    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.57/0.90    inference(ennf_transformation,[],[f15])).
% 3.57/0.90  fof(f15,axiom,(
% 3.57/0.90    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.57/0.90  fof(f207,plain,(
% 3.57/0.90    spl4_23),
% 3.57/0.90    inference(avatar_split_clause,[],[f60,f205])).
% 3.57/0.90  fof(f60,plain,(
% 3.57/0.90    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f22])).
% 3.57/0.90  fof(f22,plain,(
% 3.57/0.90    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.90    inference(ennf_transformation,[],[f10])).
% 3.57/0.90  fof(f10,axiom,(
% 3.57/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 3.57/0.90  fof(f203,plain,(
% 3.57/0.90    spl4_22),
% 3.57/0.90    inference(avatar_split_clause,[],[f77,f201])).
% 3.57/0.90  fof(f77,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/0.90    inference(cnf_transformation,[],[f32])).
% 3.57/0.90  fof(f32,plain,(
% 3.57/0.90    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.90    inference(ennf_transformation,[],[f6])).
% 3.57/0.90  fof(f6,axiom,(
% 3.57/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.57/0.90  fof(f194,plain,(
% 3.57/0.90    spl4_21 | ~spl4_4 | ~spl4_15),
% 3.57/0.90    inference(avatar_split_clause,[],[f171,f156,f103,f191])).
% 3.57/0.90  fof(f171,plain,(
% 3.57/0.90    r1_tarski(sK2,u1_struct_0(sK0)) | (~spl4_4 | ~spl4_15)),
% 3.57/0.90    inference(unit_resulting_resolution,[],[f105,f157])).
% 3.57/0.90  fof(f185,plain,(
% 3.57/0.90    spl4_20),
% 3.57/0.90    inference(avatar_split_clause,[],[f82,f183])).
% 3.57/0.90  fof(f82,plain,(
% 3.57/0.90    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f47])).
% 3.57/0.90  fof(f47,plain,(
% 3.57/0.90    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/0.90    inference(flattening,[],[f46])).
% 3.57/0.90  fof(f46,plain,(
% 3.57/0.90    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/0.90    inference(nnf_transformation,[],[f1])).
% 3.57/0.90  fof(f1,axiom,(
% 3.57/0.90    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.57/0.90  fof(f181,plain,(
% 3.57/0.90    spl4_19),
% 3.57/0.90    inference(avatar_split_clause,[],[f75,f179])).
% 3.57/0.90  fof(f75,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.57/0.90    inference(cnf_transformation,[],[f4])).
% 3.57/0.90  fof(f4,axiom,(
% 3.57/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.57/0.90  fof(f170,plain,(
% 3.57/0.90    spl4_18),
% 3.57/0.90    inference(avatar_split_clause,[],[f76,f168])).
% 3.57/0.90  fof(f76,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f31])).
% 3.57/0.90  fof(f31,plain,(
% 3.57/0.90    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.57/0.90    inference(ennf_transformation,[],[f2])).
% 3.57/0.90  fof(f2,axiom,(
% 3.57/0.90    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.57/0.90  fof(f166,plain,(
% 3.57/0.90    spl4_17),
% 3.57/0.90    inference(avatar_split_clause,[],[f74,f164])).
% 3.57/0.90  fof(f74,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.57/0.90    inference(cnf_transformation,[],[f7])).
% 3.57/0.90  fof(f7,axiom,(
% 3.57/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.57/0.90  fof(f162,plain,(
% 3.57/0.90    spl4_16),
% 3.57/0.90    inference(avatar_split_clause,[],[f84,f160])).
% 3.57/0.90  fof(f84,plain,(
% 3.57/0.90    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f48])).
% 3.57/0.90  fof(f48,plain,(
% 3.57/0.90    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.57/0.90    inference(nnf_transformation,[],[f8])).
% 3.57/0.90  fof(f8,axiom,(
% 3.57/0.90    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.57/0.90  fof(f158,plain,(
% 3.57/0.90    spl4_15),
% 3.57/0.90    inference(avatar_split_clause,[],[f83,f156])).
% 3.57/0.90  fof(f83,plain,(
% 3.57/0.90    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.57/0.90    inference(cnf_transformation,[],[f48])).
% 3.57/0.90  fof(f154,plain,(
% 3.57/0.90    spl4_14),
% 3.57/0.90    inference(avatar_split_clause,[],[f73,f152])).
% 3.57/0.90  fof(f73,plain,(
% 3.57/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f5])).
% 3.57/0.90  fof(f5,axiom,(
% 3.57/0.90    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.57/0.90  fof(f150,plain,(
% 3.57/0.90    spl4_13),
% 3.57/0.90    inference(avatar_split_clause,[],[f72,f148])).
% 3.57/0.90  fof(f72,plain,(
% 3.57/0.90    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.57/0.90    inference(cnf_transformation,[],[f3])).
% 3.57/0.90  fof(f3,axiom,(
% 3.57/0.90    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.57/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.57/0.90  fof(f146,plain,(
% 3.57/0.90    spl4_12),
% 3.57/0.90    inference(avatar_split_clause,[],[f85,f144])).
% 3.57/0.90  fof(f85,plain,(
% 3.57/0.90    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.57/0.90    inference(equality_resolution,[],[f81])).
% 3.57/0.90  fof(f81,plain,(
% 3.57/0.90    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.57/0.90    inference(cnf_transformation,[],[f47])).
% 3.57/0.90  fof(f142,plain,(
% 3.57/0.90    ~spl4_9 | ~spl4_10 | ~spl4_11),
% 3.57/0.90    inference(avatar_split_clause,[],[f59,f138,f134,f129])).
% 3.57/0.90  fof(f59,plain,(
% 3.57/0.90    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f141,plain,(
% 3.57/0.90    ~spl4_10 | ~spl4_11 | spl4_6),
% 3.57/0.90    inference(avatar_split_clause,[],[f121,f113,f138,f134])).
% 3.57/0.90  fof(f121,plain,(
% 3.57/0.90    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | spl4_6),
% 3.57/0.90    inference(subsumption_resolution,[],[f57,f114])).
% 3.57/0.90  fof(f114,plain,(
% 3.57/0.90    ~v3_pre_topc(sK3,sK1) | spl4_6),
% 3.57/0.90    inference(avatar_component_clause,[],[f113])).
% 3.57/0.90  fof(f57,plain,(
% 3.57/0.90    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f132,plain,(
% 3.57/0.90    ~spl4_9 | spl4_7),
% 3.57/0.90    inference(avatar_split_clause,[],[f56,f117,f129])).
% 3.57/0.90  fof(f56,plain,(
% 3.57/0.90    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f126,plain,(
% 3.57/0.90    spl4_8 | spl4_7),
% 3.57/0.90    inference(avatar_split_clause,[],[f55,f117,f123])).
% 3.57/0.90  fof(f55,plain,(
% 3.57/0.90    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f120,plain,(
% 3.57/0.90    spl4_6 | spl4_7),
% 3.57/0.90    inference(avatar_split_clause,[],[f54,f117,f113])).
% 3.57/0.90  fof(f54,plain,(
% 3.57/0.90    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f111,plain,(
% 3.57/0.90    spl4_5),
% 3.57/0.90    inference(avatar_split_clause,[],[f53,f108])).
% 3.57/0.90  fof(f53,plain,(
% 3.57/0.90    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f106,plain,(
% 3.57/0.90    spl4_4),
% 3.57/0.90    inference(avatar_split_clause,[],[f52,f103])).
% 3.57/0.90  fof(f52,plain,(
% 3.57/0.90    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f101,plain,(
% 3.57/0.90    spl4_3),
% 3.57/0.90    inference(avatar_split_clause,[],[f51,f98])).
% 3.57/0.90  fof(f51,plain,(
% 3.57/0.90    l1_pre_topc(sK1)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f96,plain,(
% 3.57/0.90    spl4_2),
% 3.57/0.90    inference(avatar_split_clause,[],[f50,f93])).
% 3.57/0.90  fof(f50,plain,(
% 3.57/0.90    l1_pre_topc(sK0)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  fof(f91,plain,(
% 3.57/0.90    spl4_1),
% 3.57/0.90    inference(avatar_split_clause,[],[f49,f88])).
% 3.57/0.90  fof(f49,plain,(
% 3.57/0.90    v2_pre_topc(sK0)),
% 3.57/0.90    inference(cnf_transformation,[],[f41])).
% 3.57/0.90  % SZS output end Proof for theBenchmark
% 3.57/0.90  % (32058)------------------------------
% 3.57/0.90  % (32058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.57/0.90  % (32058)Termination reason: Refutation
% 3.57/0.90  
% 3.57/0.90  % (32058)Memory used [KB]: 8315
% 3.57/0.90  % (32058)Time elapsed: 0.326 s
% 3.57/0.90  % (32058)------------------------------
% 3.57/0.90  % (32058)------------------------------
% 3.57/0.91  % (32027)Success in time 0.541 s
%------------------------------------------------------------------------------
