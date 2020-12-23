%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 314 expanded)
%              Number of leaves         :   51 ( 148 expanded)
%              Depth                    :    6
%              Number of atoms          :  576 ( 962 expanded)
%              Number of equality atoms :   63 ( 103 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f75,f79,f83,f91,f99,f103,f107,f111,f119,f123,f132,f136,f145,f149,f158,f162,f167,f171,f177,f183,f195,f200,f215,f225,f242,f258,f270,f279,f300,f325,f347,f358,f390,f404,f423])).

fof(f423,plain,
    ( ~ spl5_49
    | ~ spl5_11
    | ~ spl5_17
    | spl5_57 ),
    inference(avatar_split_clause,[],[f411,f402,f134,f105,f333])).

fof(f333,plain,
    ( spl5_49
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f105,plain,
    ( spl5_11
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f134,plain,
    ( spl5_17
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f402,plain,
    ( spl5_57
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f411,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl5_11
    | ~ spl5_17
    | spl5_57 ),
    inference(subsumption_resolution,[],[f410,f106])).

fof(f106,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f410,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl5_17
    | spl5_57 ),
    inference(superposition,[],[f403,f135])).

fof(f135,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f403,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_57 ),
    inference(avatar_component_clause,[],[f402])).

fof(f404,plain,
    ( ~ spl5_57
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_19
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f399,f388,f143,f77,f73,f402])).

fof(f73,plain,
    ( spl5_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f77,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f143,plain,
    ( spl5_19
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f388,plain,
    ( spl5_56
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f399,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_19
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f398,f74])).

fof(f74,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f398,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_19
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f396,f78])).

fof(f78,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f396,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_19
    | ~ spl5_56 ),
    inference(resolution,[],[f389,f144])).

fof(f144,plain,
    ( ! [X0] :
        ( v4_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f143])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f388])).

fof(f390,plain,
    ( spl5_56
    | ~ spl5_27
    | ~ spl5_47
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f381,f356,f323,f181,f388])).

fof(f181,plain,
    ( spl5_27
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f323,plain,
    ( spl5_47
  <=> ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f356,plain,
    ( spl5_53
  <=> ! [X3,X2] : m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f381,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_27
    | ~ spl5_47
    | ~ spl5_53 ),
    inference(trivial_inequality_removal,[],[f376])).

fof(f376,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_27
    | ~ spl5_47
    | ~ spl5_53 ),
    inference(backward_demodulation,[],[f324,f372])).

fof(f372,plain,
    ( ! [X7] : k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)
    | ~ spl5_27
    | ~ spl5_53 ),
    inference(resolution,[],[f357,f182])).

fof(f182,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f181])).

fof(f357,plain,
    ( ! [X2,X3] : m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X2))
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f356])).

fof(f324,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f323])).

fof(f358,plain,
    ( spl5_53
    | ~ spl5_11
    | ~ spl5_23
    | ~ spl5_24
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f290,f277,f165,f160,f105,f356])).

fof(f160,plain,
    ( spl5_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f165,plain,
    ( spl5_24
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f277,plain,
    ( spl5_43
  <=> ! [X1,X0] : k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f290,plain,
    ( ! [X2,X3] : m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X2))
    | ~ spl5_11
    | ~ spl5_23
    | ~ spl5_24
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f289,f286])).

fof(f286,plain,
    ( ! [X0,X1] : k9_subset_1(X0,X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl5_11
    | ~ spl5_24
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f280,f106])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(X0,X0,X1) = k3_xboole_0(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) )
    | ~ spl5_24
    | ~ spl5_43 ),
    inference(superposition,[],[f278,f166])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f165])).

fof(f278,plain,
    ( ! [X0,X1] : k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f277])).

fof(f289,plain,
    ( ! [X2,X3] : m1_subset_1(k9_subset_1(X2,X2,X3),k1_zfmisc_1(X2))
    | ~ spl5_11
    | ~ spl5_23
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f283,f106])).

fof(f283,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k9_subset_1(X2,X2,X3),k1_zfmisc_1(X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X2)) )
    | ~ spl5_23
    | ~ spl5_43 ),
    inference(superposition,[],[f161,f278])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f160])).

fof(f347,plain,
    ( ~ spl5_4
    | ~ spl5_10
    | spl5_49 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_10
    | spl5_49 ),
    inference(subsumption_resolution,[],[f344,f78])).

fof(f344,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_10
    | spl5_49 ),
    inference(resolution,[],[f334,f102])).

fof(f102,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_10
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f334,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_49 ),
    inference(avatar_component_clause,[],[f333])).

fof(f325,plain,
    ( spl5_47
    | ~ spl5_9
    | ~ spl5_24
    | ~ spl5_42
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f310,f298,f268,f165,f97,f323])).

fof(f97,plain,
    ( spl5_9
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f268,plain,
    ( spl5_42
  <=> ! [X0] :
        ( k1_xboole_0 != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f298,plain,
    ( spl5_45
  <=> ! [X3,X2] : k9_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f310,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_9
    | ~ spl5_24
    | ~ spl5_42
    | ~ spl5_45 ),
    inference(backward_demodulation,[],[f269,f308])).

fof(f308,plain,
    ( ! [X2,X3] : k9_subset_1(X2,k1_xboole_0,X3) = k3_xboole_0(X3,k1_xboole_0)
    | ~ spl5_9
    | ~ spl5_24
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f301,f98])).

fof(f98,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f301,plain,
    ( ! [X2,X3] :
        ( k9_subset_1(X2,k1_xboole_0,X3) = k3_xboole_0(X3,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) )
    | ~ spl5_24
    | ~ spl5_45 ),
    inference(superposition,[],[f299,f166])).

fof(f299,plain,
    ( ! [X2,X3] : k9_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,k1_xboole_0,X3)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f298])).

fof(f269,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f268])).

fof(f300,plain,
    ( spl5_45
    | ~ spl5_9
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f185,f175,f97,f298])).

fof(f175,plain,
    ( spl5_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f185,plain,
    ( ! [X2,X3] : k9_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,k1_xboole_0,X3)
    | ~ spl5_9
    | ~ spl5_26 ),
    inference(resolution,[],[f176,f98])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f175])).

fof(f279,plain,
    ( spl5_43
    | ~ spl5_11
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f184,f175,f105,f277])).

fof(f184,plain,
    ( ! [X0,X1] : k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1)
    | ~ spl5_11
    | ~ spl5_26 ),
    inference(resolution,[],[f176,f106])).

fof(f270,plain,
    ( spl5_42
    | ~ spl5_9
    | spl5_16
    | ~ spl5_37
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f262,f256,f240,f130,f97,f268])).

fof(f130,plain,
    ( spl5_16
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f240,plain,
    ( spl5_37
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f256,plain,
    ( spl5_40
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | sK2(sK0,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1)
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f262,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_9
    | spl5_16
    | ~ spl5_37
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f261,f241])).

fof(f241,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f240])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | sK2(sK0,k1_xboole_0) != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0) )
    | ~ spl5_9
    | spl5_16
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f260,f98])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | sK2(sK0,k1_xboole_0) != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_16
    | ~ spl5_40 ),
    inference(resolution,[],[f257,f131])).

fof(f131,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | sK2(sK0,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl5_40
    | ~ spl5_4
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f238,f223,f77,f256])).

fof(f223,plain,
    ( spl5_34
  <=> ! [X1,X3,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X3,X0)
        | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | sK2(sK0,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1)
        | v2_tex_2(X0,sK0) )
    | ~ spl5_4
    | ~ spl5_34 ),
    inference(resolution,[],[f224,f78])).

fof(f224,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X3,X0)
        | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
        | v2_tex_2(X1,X0) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f223])).

fof(f242,plain,
    ( spl5_37
    | ~ spl5_14
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f216,f213,f117,f240])).

fof(f117,plain,
    ( spl5_14
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f213,plain,
    ( spl5_32
  <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f216,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_14
    | ~ spl5_32 ),
    inference(resolution,[],[f214,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f214,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f213])).

fof(f225,plain,(
    spl5_34 ),
    inference(avatar_split_clause,[],[f47,f223])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

% (18091)Refutation not found, incomplete strategy% (18091)------------------------------
% (18091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18091)Termination reason: Refutation not found, incomplete strategy

% (18091)Memory used [KB]: 10618
% (18091)Time elapsed: 0.109 s
% (18091)------------------------------
% (18091)------------------------------
fof(f215,plain,
    ( spl5_32
    | ~ spl5_9
    | spl5_16
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f206,f198,f130,f97,f213])).

fof(f198,plain,
    ( spl5_29
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f206,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_9
    | spl5_16
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f205,f98])).

fof(f205,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_16
    | ~ spl5_29 ),
    inference(resolution,[],[f199,f131])).

fof(f199,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | r1_tarski(sK2(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl5_29
    | ~ spl5_4
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f196,f193,f77,f198])).

fof(f193,plain,
    ( spl5_28
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0) )
    | ~ spl5_4
    | ~ spl5_28 ),
    inference(resolution,[],[f194,f78])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,(
    spl5_28 ),
    inference(avatar_split_clause,[],[f52,f193])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f183,plain,
    ( spl5_27
    | ~ spl5_12
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f173,f169,f109,f181])).

fof(f109,plain,
    ( spl5_12
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f169,plain,
    ( spl5_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f173,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 )
    | ~ spl5_12
    | ~ spl5_25 ),
    inference(resolution,[],[f170,f110])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f170,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f169])).

fof(f177,plain,(
    spl5_26 ),
    inference(avatar_split_clause,[],[f60,f175])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f171,plain,
    ( spl5_25
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f163,f156,f121,f169])).

fof(f121,plain,
    ( spl5_15
  <=> ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f156,plain,
    ( spl5_22
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(resolution,[],[f157,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f156])).

fof(f167,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f59,f165])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f162,plain,(
    spl5_23 ),
    inference(avatar_split_clause,[],[f58,f160])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f158,plain,
    ( spl5_22
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f154,f147,f89,f156])).

fof(f89,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f147,plain,
    ( spl5_20
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(resolution,[],[f148,f90])).

fof(f90,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f62,f147])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f145,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f55,f143])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f136,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f45,f134])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f132,plain,
    ( ~ spl5_16
    | ~ spl5_1
    | spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f127,f109,f81,f65,f130])).

fof(f65,plain,
    ( spl5_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f81,plain,
    ( spl5_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f127,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | ~ spl5_1
    | spl5_5
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f82,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_1
    | ~ spl5_12 ),
    inference(resolution,[],[f110,f66])).

fof(f66,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f82,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f123,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f56,f121])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f119,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f54,f117])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f111,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f53,f109])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f107,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f63,f105])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f44,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f103,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f46,f101])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f99,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f91,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f41,f89])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f83,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f79,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:17:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (18095)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (18085)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (18087)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (18082)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (18093)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (18084)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (18083)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (18088)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (18089)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (18090)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (18086)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (18099)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (18096)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (18081)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (18080)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (18081)Refutation not found, incomplete strategy% (18081)------------------------------
% 0.22/0.51  % (18081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18081)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18081)Memory used [KB]: 10618
% 0.22/0.51  % (18081)Time elapsed: 0.097 s
% 0.22/0.51  % (18081)------------------------------
% 0.22/0.51  % (18081)------------------------------
% 0.22/0.51  % (18080)Refutation not found, incomplete strategy% (18080)------------------------------
% 0.22/0.51  % (18080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18080)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18080)Memory used [KB]: 6140
% 0.22/0.51  % (18080)Time elapsed: 0.087 s
% 0.22/0.51  % (18080)------------------------------
% 0.22/0.51  % (18080)------------------------------
% 0.22/0.51  % (18098)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (18100)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (18100)Refutation not found, incomplete strategy% (18100)------------------------------
% 0.22/0.52  % (18100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18100)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18100)Memory used [KB]: 10618
% 0.22/0.52  % (18100)Time elapsed: 0.099 s
% 0.22/0.52  % (18100)------------------------------
% 0.22/0.52  % (18100)------------------------------
% 0.22/0.52  % (18092)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18089)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (18097)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (18091)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f424,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f67,f75,f79,f83,f91,f99,f103,f107,f111,f119,f123,f132,f136,f145,f149,f158,f162,f167,f171,f177,f183,f195,f200,f215,f225,f242,f258,f270,f279,f300,f325,f347,f358,f390,f404,f423])).
% 0.22/0.52  fof(f423,plain,(
% 0.22/0.52    ~spl5_49 | ~spl5_11 | ~spl5_17 | spl5_57),
% 0.22/0.52    inference(avatar_split_clause,[],[f411,f402,f134,f105,f333])).
% 0.22/0.52  fof(f333,plain,(
% 0.22/0.52    spl5_49 <=> l1_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    spl5_11 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    spl5_17 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.52  fof(f402,plain,(
% 0.22/0.52    spl5_57 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 0.22/0.52  fof(f411,plain,(
% 0.22/0.52    ~l1_struct_0(sK0) | (~spl5_11 | ~spl5_17 | spl5_57)),
% 0.22/0.52    inference(subsumption_resolution,[],[f410,f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl5_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f105])).
% 0.22/0.52  fof(f410,plain,(
% 0.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | (~spl5_17 | spl5_57)),
% 0.22/0.52    inference(superposition,[],[f403,f135])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) ) | ~spl5_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f134])).
% 0.22/0.52  fof(f403,plain,(
% 0.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_57),
% 0.22/0.52    inference(avatar_component_clause,[],[f402])).
% 0.22/0.52  fof(f404,plain,(
% 0.22/0.52    ~spl5_57 | ~spl5_3 | ~spl5_4 | ~spl5_19 | ~spl5_56),
% 0.22/0.52    inference(avatar_split_clause,[],[f399,f388,f143,f77,f73,f402])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl5_3 <=> v2_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl5_4 <=> l1_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    spl5_19 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.52  fof(f388,plain,(
% 0.22/0.52    spl5_56 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 0.22/0.52  fof(f399,plain,(
% 0.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_3 | ~spl5_4 | ~spl5_19 | ~spl5_56)),
% 0.22/0.52    inference(subsumption_resolution,[],[f398,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    v2_pre_topc(sK0) | ~spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f398,plain,(
% 0.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | (~spl5_4 | ~spl5_19 | ~spl5_56)),
% 0.22/0.52    inference(subsumption_resolution,[],[f396,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    l1_pre_topc(sK0) | ~spl5_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f396,plain,(
% 0.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_19 | ~spl5_56)),
% 0.22/0.52    inference(resolution,[],[f389,f144])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl5_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f143])).
% 0.22/0.52  fof(f389,plain,(
% 0.22/0.52    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_56),
% 0.22/0.52    inference(avatar_component_clause,[],[f388])).
% 0.22/0.52  fof(f390,plain,(
% 0.22/0.52    spl5_56 | ~spl5_27 | ~spl5_47 | ~spl5_53),
% 0.22/0.52    inference(avatar_split_clause,[],[f381,f356,f323,f181,f388])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    spl5_27 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.52  fof(f323,plain,(
% 0.22/0.52    spl5_47 <=> ! [X0] : (k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.22/0.52  fof(f356,plain,(
% 0.22/0.52    spl5_53 <=> ! [X3,X2] : m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.22/0.52  fof(f381,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | (~spl5_27 | ~spl5_47 | ~spl5_53)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f376])).
% 0.22/0.52  fof(f376,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | (~spl5_27 | ~spl5_47 | ~spl5_53)),
% 0.22/0.52    inference(backward_demodulation,[],[f324,f372])).
% 0.22/0.52  fof(f372,plain,(
% 0.22/0.52    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)) ) | (~spl5_27 | ~spl5_53)),
% 0.22/0.52    inference(resolution,[],[f357,f182])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3) ) | ~spl5_27),
% 0.22/0.52    inference(avatar_component_clause,[],[f181])).
% 0.22/0.52  fof(f357,plain,(
% 0.22/0.52    ( ! [X2,X3] : (m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X2))) ) | ~spl5_53),
% 0.22/0.52    inference(avatar_component_clause,[],[f356])).
% 0.22/0.52  fof(f324,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | ~spl5_47),
% 0.22/0.52    inference(avatar_component_clause,[],[f323])).
% 0.22/0.52  fof(f358,plain,(
% 0.22/0.52    spl5_53 | ~spl5_11 | ~spl5_23 | ~spl5_24 | ~spl5_43),
% 0.22/0.52    inference(avatar_split_clause,[],[f290,f277,f165,f160,f105,f356])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    spl5_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    spl5_24 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    spl5_43 <=> ! [X1,X0] : k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    ( ! [X2,X3] : (m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X2))) ) | (~spl5_11 | ~spl5_23 | ~spl5_24 | ~spl5_43)),
% 0.22/0.52    inference(forward_demodulation,[],[f289,f286])).
% 0.22/0.52  fof(f286,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_subset_1(X0,X0,X1) = k3_xboole_0(X1,X0)) ) | (~spl5_11 | ~spl5_24 | ~spl5_43)),
% 0.22/0.52    inference(subsumption_resolution,[],[f280,f106])).
% 0.22/0.52  fof(f280,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_subset_1(X0,X0,X1) = k3_xboole_0(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl5_24 | ~spl5_43)),
% 0.22/0.52    inference(superposition,[],[f278,f166])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl5_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f165])).
% 0.22/0.52  fof(f278,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1)) ) | ~spl5_43),
% 0.22/0.52    inference(avatar_component_clause,[],[f277])).
% 0.22/0.52  fof(f289,plain,(
% 0.22/0.52    ( ! [X2,X3] : (m1_subset_1(k9_subset_1(X2,X2,X3),k1_zfmisc_1(X2))) ) | (~spl5_11 | ~spl5_23 | ~spl5_43)),
% 0.22/0.52    inference(subsumption_resolution,[],[f283,f106])).
% 0.22/0.52  fof(f283,plain,(
% 0.22/0.52    ( ! [X2,X3] : (m1_subset_1(k9_subset_1(X2,X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X2))) ) | (~spl5_23 | ~spl5_43)),
% 0.22/0.52    inference(superposition,[],[f161,f278])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl5_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f160])).
% 0.22/0.52  fof(f347,plain,(
% 0.22/0.52    ~spl5_4 | ~spl5_10 | spl5_49),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f346])).
% 0.22/0.52  fof(f346,plain,(
% 0.22/0.52    $false | (~spl5_4 | ~spl5_10 | spl5_49)),
% 0.22/0.52    inference(subsumption_resolution,[],[f344,f78])).
% 0.22/0.52  fof(f344,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | (~spl5_10 | spl5_49)),
% 0.22/0.52    inference(resolution,[],[f334,f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl5_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f101])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl5_10 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.52  fof(f334,plain,(
% 0.22/0.52    ~l1_struct_0(sK0) | spl5_49),
% 0.22/0.52    inference(avatar_component_clause,[],[f333])).
% 0.22/0.52  fof(f325,plain,(
% 0.22/0.52    spl5_47 | ~spl5_9 | ~spl5_24 | ~spl5_42 | ~spl5_45),
% 0.22/0.52    inference(avatar_split_clause,[],[f310,f298,f268,f165,f97,f323])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl5_9 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    spl5_42 <=> ! [X0] : (k1_xboole_0 != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.22/0.52  fof(f298,plain,(
% 0.22/0.52    spl5_45 <=> ! [X3,X2] : k9_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,k1_xboole_0,X3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.22/0.52  fof(f310,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | (~spl5_9 | ~spl5_24 | ~spl5_42 | ~spl5_45)),
% 0.22/0.52    inference(backward_demodulation,[],[f269,f308])).
% 0.22/0.52  fof(f308,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k9_subset_1(X2,k1_xboole_0,X3) = k3_xboole_0(X3,k1_xboole_0)) ) | (~spl5_9 | ~spl5_24 | ~spl5_45)),
% 0.22/0.52    inference(subsumption_resolution,[],[f301,f98])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl5_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f97])).
% 0.22/0.52  fof(f301,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k9_subset_1(X2,k1_xboole_0,X3) = k3_xboole_0(X3,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))) ) | (~spl5_24 | ~spl5_45)),
% 0.22/0.52    inference(superposition,[],[f299,f166])).
% 0.22/0.52  fof(f299,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k9_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,k1_xboole_0,X3)) ) | ~spl5_45),
% 0.22/0.52    inference(avatar_component_clause,[],[f298])).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | ~spl5_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f268])).
% 0.22/0.52  fof(f300,plain,(
% 0.22/0.52    spl5_45 | ~spl5_9 | ~spl5_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f185,f175,f97,f298])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    spl5_26 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k9_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,k1_xboole_0,X3)) ) | (~spl5_9 | ~spl5_26)),
% 0.22/0.52    inference(resolution,[],[f176,f98])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) ) | ~spl5_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f175])).
% 0.22/0.52  fof(f279,plain,(
% 0.22/0.52    spl5_43 | ~spl5_11 | ~spl5_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f184,f175,f105,f277])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1)) ) | (~spl5_11 | ~spl5_26)),
% 0.22/0.52    inference(resolution,[],[f176,f106])).
% 0.22/0.52  fof(f270,plain,(
% 0.22/0.52    spl5_42 | ~spl5_9 | spl5_16 | ~spl5_37 | ~spl5_40),
% 0.22/0.52    inference(avatar_split_clause,[],[f262,f256,f240,f130,f97,f268])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    spl5_16 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    spl5_37 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    spl5_40 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | sK2(sK0,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1) | v2_tex_2(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | (~spl5_9 | spl5_16 | ~spl5_37 | ~spl5_40)),
% 0.22/0.52    inference(forward_demodulation,[],[f261,f241])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl5_37),
% 0.22/0.52    inference(avatar_component_clause,[],[f240])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | sK2(sK0,k1_xboole_0) != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)) ) | (~spl5_9 | spl5_16 | ~spl5_40)),
% 0.22/0.52    inference(subsumption_resolution,[],[f260,f98])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | sK2(sK0,k1_xboole_0) != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_16 | ~spl5_40)),
% 0.22/0.52    inference(resolution,[],[f257,f131])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ~v2_tex_2(k1_xboole_0,sK0) | spl5_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f130])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_tex_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | sK2(sK0,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_40),
% 0.22/0.52    inference(avatar_component_clause,[],[f256])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    spl5_40 | ~spl5_4 | ~spl5_34),
% 0.22/0.52    inference(avatar_split_clause,[],[f238,f223,f77,f256])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    spl5_34 <=> ! [X1,X3,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.22/0.52  fof(f238,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | sK2(sK0,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1) | v2_tex_2(X0,sK0)) ) | (~spl5_4 | ~spl5_34)),
% 0.22/0.52    inference(resolution,[],[f224,f78])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) ) | ~spl5_34),
% 0.22/0.52    inference(avatar_component_clause,[],[f223])).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    spl5_37 | ~spl5_14 | ~spl5_32),
% 0.22/0.52    inference(avatar_split_clause,[],[f216,f213,f117,f240])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    spl5_14 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    spl5_32 <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    k1_xboole_0 = sK2(sK0,k1_xboole_0) | (~spl5_14 | ~spl5_32)),
% 0.22/0.52    inference(resolution,[],[f214,f118])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl5_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f117])).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | ~spl5_32),
% 0.22/0.52    inference(avatar_component_clause,[],[f213])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    spl5_34),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f223])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.22/0.52  % (18091)Refutation not found, incomplete strategy% (18091)------------------------------
% 0.22/0.52  % (18091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18091)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18091)Memory used [KB]: 10618
% 0.22/0.52  % (18091)Time elapsed: 0.109 s
% 0.22/0.52  % (18091)------------------------------
% 0.22/0.52  % (18091)------------------------------
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    spl5_32 | ~spl5_9 | spl5_16 | ~spl5_29),
% 0.22/0.52    inference(avatar_split_clause,[],[f206,f198,f130,f97,f213])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    spl5_29 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | (~spl5_9 | spl5_16 | ~spl5_29)),
% 0.22/0.52    inference(subsumption_resolution,[],[f205,f98])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_16 | ~spl5_29)),
% 0.22/0.52    inference(resolution,[],[f199,f131])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    ( ! [X0] : (v2_tex_2(X0,sK0) | r1_tarski(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_29),
% 0.22/0.52    inference(avatar_component_clause,[],[f198])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    spl5_29 | ~spl5_4 | ~spl5_28),
% 0.22/0.52    inference(avatar_split_clause,[],[f196,f193,f77,f198])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    spl5_28 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0)) ) | (~spl5_4 | ~spl5_28)),
% 0.22/0.52    inference(resolution,[],[f194,f78])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) ) | ~spl5_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f193])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    spl5_28),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f193])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    spl5_27 | ~spl5_12 | ~spl5_25),
% 0.22/0.52    inference(avatar_split_clause,[],[f173,f169,f109,f181])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl5_12 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl5_25 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3) ) | (~spl5_12 | ~spl5_25)),
% 0.22/0.52    inference(resolution,[],[f170,f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f109])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_25),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    spl5_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f60,f175])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    spl5_25 | ~spl5_15 | ~spl5_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f163,f156,f121,f169])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl5_15 <=> ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    spl5_22 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | (~spl5_15 | ~spl5_22)),
% 0.22/0.53    inference(resolution,[],[f157,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) ) | ~spl5_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f121])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f156])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    spl5_24),
% 0.22/0.53    inference(avatar_split_clause,[],[f59,f165])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    spl5_23),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f160])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    spl5_22 | ~spl5_7 | ~spl5_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f154,f147,f89,f156])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl5_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl5_20 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | (~spl5_7 | ~spl5_20)),
% 0.22/0.53    inference(resolution,[],[f148,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0) | ~spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl5_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f147])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl5_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f62,f147])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    spl5_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f143])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    spl5_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f134])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ~spl5_16 | ~spl5_1 | spl5_5 | ~spl5_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f127,f109,f81,f65,f130])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl5_1 <=> v1_xboole_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl5_5 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ~v2_tex_2(k1_xboole_0,sK0) | (~spl5_1 | spl5_5 | ~spl5_12)),
% 0.22/0.53    inference(backward_demodulation,[],[f82,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | (~spl5_1 | ~spl5_12)),
% 0.22/0.53    inference(resolution,[],[f110,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    v1_xboole_0(sK1) | ~spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f65])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ~v2_tex_2(sK1,sK0) | spl5_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f81])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl5_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f56,f121])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    spl5_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f54,f117])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl5_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f53,f109])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl5_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f63,f105])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f44,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f46,f101])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl5_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f97])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f89])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ~spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f81])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ~v2_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f17])).
% 0.22/0.53  fof(f17,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f77])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f73])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl5_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f65])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    v1_xboole_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (18089)------------------------------
% 0.22/0.53  % (18089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18089)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (18089)Memory used [KB]: 10874
% 0.22/0.53  % (18089)Time elapsed: 0.086 s
% 0.22/0.53  % (18089)------------------------------
% 0.22/0.53  % (18089)------------------------------
% 0.22/0.53  % (18079)Success in time 0.163 s
%------------------------------------------------------------------------------
