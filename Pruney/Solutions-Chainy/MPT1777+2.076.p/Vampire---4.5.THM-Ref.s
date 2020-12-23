%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:14 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  327 ( 649 expanded)
%              Number of leaves         :   77 ( 290 expanded)
%              Depth                    :   13
%              Number of atoms          : 1726 (4008 expanded)
%              Number of equality atoms :   46 ( 259 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f94,f98,f102,f106,f110,f114,f118,f122,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f178,f182,f187,f195,f199,f208,f212,f216,f227,f242,f249,f275,f284,f312,f324,f359,f371,f429,f437,f467,f509,f525,f547,f562,f591,f617,f643,f647,f671,f675,f913,f1045,f1069,f1100,f1122,f1163,f1172,f1175,f1292,f1427,f1510,f1536])).

fof(f1536,plain,
    ( ~ spl7_81
    | ~ spl7_183
    | ~ spl7_162
    | spl7_3
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_194 ),
    inference(avatar_split_clause,[],[f1518,f1508,f180,f168,f96,f1265,f1408,f576])).

fof(f576,plain,
    ( spl7_81
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f1408,plain,
    ( spl7_183
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).

fof(f1265,plain,
    ( spl7_162
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f96,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f168,plain,
    ( spl7_21
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_pre_topc(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f180,plain,
    ( spl7_24
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1508,plain,
    ( spl7_194
  <=> ! [X2] :
        ( ~ v3_pre_topc(k2_struct_0(sK2),X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_194])])).

fof(f1518,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | spl7_3
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_194 ),
    inference(subsumption_resolution,[],[f1517,f169])).

fof(f169,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f168])).

fof(f1517,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | spl7_3
    | ~ spl7_24
    | ~ spl7_194 ),
    inference(subsumption_resolution,[],[f1516,f97])).

fof(f97,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f1516,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl7_24
    | ~ spl7_194 ),
    inference(duplicate_literal_removal,[],[f1515])).

fof(f1515,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_24
    | ~ spl7_194 ),
    inference(resolution,[],[f1509,f181])).

fof(f181,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1509,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(k2_struct_0(sK2),X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl7_194 ),
    inference(avatar_component_clause,[],[f1508])).

fof(f1510,plain,
    ( spl7_194
    | ~ spl7_37
    | ~ spl7_92
    | ~ spl7_150 ),
    inference(avatar_split_clause,[],[f1184,f1169,f673,f247,f1508])).

fof(f247,plain,
    ( spl7_37
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v3_pre_topc(u1_struct_0(X1),X0)
        | v1_tsep_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f673,plain,
    ( spl7_92
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f1169,plain,
    ( spl7_150
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f1184,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(k2_struct_0(sK2),X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl7_37
    | ~ spl7_92
    | ~ spl7_150 ),
    inference(forward_demodulation,[],[f1178,f674])).

fof(f674,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f673])).

fof(f1178,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v3_pre_topc(u1_struct_0(sK2),X2) )
    | ~ spl7_37
    | ~ spl7_150 ),
    inference(duplicate_literal_removal,[],[f1177])).

fof(f1177,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v3_pre_topc(u1_struct_0(sK2),X2)
        | ~ v2_pre_topc(X2) )
    | ~ spl7_37
    | ~ spl7_150 ),
    inference(resolution,[],[f1170,f248])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( v1_tsep_1(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v3_pre_topc(u1_struct_0(X1),X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f247])).

fof(f1170,plain,
    ( ! [X0] :
        ( ~ v1_tsep_1(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_150 ),
    inference(avatar_component_clause,[],[f1169])).

fof(f1427,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_25
    | spl7_183 ),
    inference(avatar_contradiction_clause,[],[f1425])).

fof(f1425,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_25
    | spl7_183 ),
    inference(unit_resulting_resolution,[],[f117,f121,f133,f1409,f186])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl7_25
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1409,plain,
    ( ~ v2_pre_topc(sK2)
    | spl7_183 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f133,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1292,plain,
    ( ~ spl7_81
    | ~ spl7_144
    | ~ spl7_28
    | ~ spl7_91
    | ~ spl7_92
    | spl7_162 ),
    inference(avatar_split_clause,[],[f1287,f1265,f673,f669,f197,f1136,f576])).

fof(f1136,plain,
    ( spl7_144
  <=> m1_pre_topc(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f197,plain,
    ( spl7_28
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | m1_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f669,plain,
    ( spl7_91
  <=> sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f1287,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl7_28
    | ~ spl7_91
    | ~ spl7_92
    | spl7_162 ),
    inference(forward_demodulation,[],[f1286,f670])).

fof(f670,plain,
    ( sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f669])).

fof(f1286,plain,
    ( ~ m1_pre_topc(sK3,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_28
    | ~ spl7_92
    | spl7_162 ),
    inference(forward_demodulation,[],[f1283,f674])).

fof(f1283,plain,
    ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_28
    | spl7_162 ),
    inference(resolution,[],[f1266,f198])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f197])).

fof(f1266,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | spl7_162 ),
    inference(avatar_component_clause,[],[f1265])).

fof(f1175,plain,
    ( ~ spl7_9
    | ~ spl7_11
    | ~ spl7_23
    | spl7_148 ),
    inference(avatar_contradiction_clause,[],[f1173])).

fof(f1173,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_23
    | spl7_148 ),
    inference(unit_resulting_resolution,[],[f121,f129,f1162,f177])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl7_23
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1162,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_148 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1161,plain,
    ( spl7_148
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f129,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1172,plain,
    ( spl7_150
    | ~ spl7_142
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_88
    | ~ spl7_92
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f930,f911,f673,f641,f160,f128,f120,f116,f112,f96,f1120,f1169])).

fof(f1120,plain,
    ( spl7_142
  <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f112,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f160,plain,
    ( spl7_19
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f641,plain,
    ( spl7_88
  <=> m1_subset_1(sK5,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f911,plain,
    ( spl7_120
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(u1_struct_0(X0),k2_struct_0(sK3))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f930,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_88
    | ~ spl7_92
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f929,f674])).

fof(f929,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_88
    | ~ spl7_92
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f928,f642])).

fof(f642,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f641])).

fof(f928,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_92
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f927,f674])).

fof(f927,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f926,f117])).

fof(f926,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | spl7_3
    | spl7_7
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f925,f121])).

fof(f925,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | spl7_3
    | spl7_7
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f924,f113])).

fof(f113,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f924,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | spl7_3
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f923,f129])).

fof(f923,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | spl7_3
    | ~ spl7_19
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f918,f97])).

fof(f918,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))
        | ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | ~ spl7_19
    | ~ spl7_120 ),
    inference(resolution,[],[f912,f161])).

fof(f161,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f912,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(u1_struct_0(X0),k2_struct_0(sK3))
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X2) )
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f911])).

fof(f1163,plain,
    ( ~ spl7_148
    | ~ spl7_21
    | spl7_144 ),
    inference(avatar_split_clause,[],[f1150,f1136,f168,f1161])).

fof(f1150,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl7_21
    | spl7_144 ),
    inference(resolution,[],[f1137,f169])).

fof(f1137,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | spl7_144 ),
    inference(avatar_component_clause,[],[f1136])).

fof(f1122,plain,
    ( ~ spl7_133
    | spl7_142
    | ~ spl7_92
    | ~ spl7_139 ),
    inference(avatar_split_clause,[],[f1113,f1098,f673,f1120,f1029])).

fof(f1029,plain,
    ( spl7_133
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).

fof(f1098,plain,
    ( spl7_139
  <=> ! [X4] :
        ( r1_tarski(u1_struct_0(X4),k2_struct_0(sK3))
        | ~ m1_pre_topc(X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).

fof(f1113,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl7_92
    | ~ spl7_139 ),
    inference(superposition,[],[f1099,f674])).

fof(f1099,plain,
    ( ! [X4] :
        ( r1_tarski(u1_struct_0(X4),k2_struct_0(sK3))
        | ~ m1_pre_topc(X4,sK3) )
    | ~ spl7_139 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f1100,plain,
    ( spl7_139
    | ~ spl7_11
    | ~ spl7_63
    | ~ spl7_89 ),
    inference(avatar_split_clause,[],[f666,f645,f427,f128,f1098])).

fof(f427,plain,
    ( spl7_63
  <=> ! [X3,X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X3,X2)
        | r1_tarski(u1_struct_0(X3),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f645,plain,
    ( spl7_89
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f666,plain,
    ( ! [X4] :
        ( r1_tarski(u1_struct_0(X4),k2_struct_0(sK3))
        | ~ m1_pre_topc(X4,sK3) )
    | ~ spl7_11
    | ~ spl7_63
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f658,f129])).

fof(f658,plain,
    ( ! [X4] :
        ( r1_tarski(u1_struct_0(X4),k2_struct_0(sK3))
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl7_63
    | ~ spl7_89 ),
    inference(superposition,[],[f428,f646])).

fof(f646,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f645])).

fof(f428,plain,
    ( ! [X2,X3] :
        ( r1_tarski(u1_struct_0(X3),u1_struct_0(X2))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f427])).

fof(f1069,plain,
    ( ~ spl7_81
    | ~ spl7_21
    | spl7_135 ),
    inference(avatar_split_clause,[],[f1059,f1043,f168,f576])).

fof(f1043,plain,
    ( spl7_135
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f1059,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl7_21
    | spl7_135 ),
    inference(resolution,[],[f1044,f169])).

fof(f1044,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl7_135 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1045,plain,
    ( ~ spl7_135
    | ~ spl7_75
    | spl7_133 ),
    inference(avatar_split_clause,[],[f1035,f1029,f523,f1043])).

fof(f523,plain,
    ( spl7_75
  <=> ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1035,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ spl7_75
    | spl7_133 ),
    inference(resolution,[],[f1030,f524])).

fof(f524,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f523])).

fof(f1030,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl7_133 ),
    inference(avatar_component_clause,[],[f1029])).

fof(f913,plain,
    ( spl7_120
    | spl7_2
    | ~ spl7_11
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_80
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f628,f615,f560,f322,f310,f128,f92,f911])).

fof(f92,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f310,plain,
    ( spl7_46
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X1,X2)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f322,plain,
    ( spl7_47
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
        | v1_tsep_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f560,plain,
    ( spl7_80
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f615,plain,
    ( spl7_86
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) = k2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f628,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(u1_struct_0(X0),k2_struct_0(sK3))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X2) )
    | spl7_2
    | ~ spl7_11
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_80
    | ~ spl7_86 ),
    inference(backward_demodulation,[],[f572,f618])).

fof(f618,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl7_11
    | ~ spl7_86 ),
    inference(resolution,[],[f616,f129])).

fof(f616,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) = k2_struct_0(X1) )
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f615])).

fof(f572,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))
        | v2_struct_0(X2) )
    | spl7_2
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f571,f311])).

fof(f311,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(X1,X2)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) )
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f310])).

fof(f571,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))
        | v2_struct_0(X2) )
    | spl7_2
    | ~ spl7_47
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f568,f93])).

fof(f93,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f568,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X2)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))
        | v2_struct_0(X2) )
    | ~ spl7_47
    | ~ spl7_80 ),
    inference(resolution,[],[f561,f323])).

fof(f323,plain,
    ( ! [X2,X0,X1] :
        ( v1_tsep_1(X1,X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
        | v2_struct_0(X0) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f322])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(X1,sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f560])).

fof(f675,plain,
    ( spl7_92
    | ~ spl7_12
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f619,f615,f132,f673])).

fof(f619,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_12
    | ~ spl7_86 ),
    inference(resolution,[],[f616,f133])).

fof(f671,plain,
    ( spl7_91
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f632,f615,f152,f132,f669])).

fof(f152,plain,
    ( spl7_17
  <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f632,plain,
    ( sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_86 ),
    inference(backward_demodulation,[],[f153,f619])).

fof(f153,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f647,plain,
    ( spl7_89
    | ~ spl7_11
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f618,f615,f128,f645])).

fof(f643,plain,
    ( spl7_88
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f633,f615,f140,f132,f641])).

fof(f140,plain,
    ( spl7_14
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f633,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2))
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_86 ),
    inference(backward_demodulation,[],[f141,f619])).

fof(f141,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f617,plain,
    ( spl7_86
    | ~ spl7_9
    | ~ spl7_79 ),
    inference(avatar_split_clause,[],[f557,f545,f120,f615])).

fof(f545,plain,
    ( spl7_79
  <=> ! [X1,X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f557,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) = k2_struct_0(X1) )
    | ~ spl7_9
    | ~ spl7_79 ),
    inference(resolution,[],[f546,f121])).

fof(f546,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,X1)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl7_79 ),
    inference(avatar_component_clause,[],[f545])).

fof(f591,plain,
    ( ~ spl7_9
    | ~ spl7_12
    | ~ spl7_23
    | spl7_81 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_23
    | spl7_81 ),
    inference(unit_resulting_resolution,[],[f121,f133,f577,f177])).

fof(f577,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_81 ),
    inference(avatar_component_clause,[],[f576])).

fof(f562,plain,
    ( spl7_80
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_29
    | ~ spl7_30
    | ~ spl7_31
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f479,f465,f214,f210,f206,f144,f136,f108,f104,f100,f92,f560])).

fof(f100,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f104,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f108,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f136,plain,
    ( spl7_13
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f144,plain,
    ( spl7_15
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f206,plain,
    ( spl7_29
  <=> v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f210,plain,
    ( spl7_30
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f214,plain,
    ( spl7_31
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f465,plain,
    ( spl7_68
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f479,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_29
    | ~ spl7_30
    | ~ spl7_31
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f478,f215])).

fof(f215,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f214])).

fof(f478,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_29
    | ~ spl7_30
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f477,f211])).

fof(f211,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f210])).

fof(f477,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_29
    | ~ spl7_30
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f476,f207])).

fof(f207,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f206])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_30
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f475,f211])).

fof(f475,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f474,f137])).

fof(f137,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f474,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f473,f93])).

fof(f473,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f472,f109])).

fof(f109,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f472,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_4
    | ~ spl7_5
    | spl7_15
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f471,f105])).

fof(f105,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f471,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_4
    | spl7_15
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f470,f101])).

fof(f101,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f470,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | spl7_15
    | ~ spl7_68 ),
    inference(resolution,[],[f466,f145])).

fof(f145,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f466,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r1_tmap_1(X3,X1,sK4,X4)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f465])).

fof(f547,plain,
    ( spl7_79
    | ~ spl7_23
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f202,f193,f176,f545])).

fof(f193,plain,
    ( spl7_27
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl7_23
    | ~ spl7_27 ),
    inference(resolution,[],[f194,f177])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f193])).

fof(f525,plain,
    ( spl7_75
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f517,f507,f152,f132,f523])).

fof(f507,plain,
    ( spl7_73
  <=> ! [X3,X2] :
        ( ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,sK0)
        | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f517,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f516,f133])).

fof(f516,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_17
    | ~ spl7_73 ),
    inference(superposition,[],[f508,f153])).

fof(f508,plain,
    ( ! [X2,X3] :
        ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,X3) )
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f507])).

fof(f509,plain,
    ( spl7_73
    | ~ spl7_9
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f443,f435,f120,f507])).

fof(f435,plain,
    ( spl7_64
  <=> ! [X3,X2,X4] :
        ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,X4)
        | ~ l1_pre_topc(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f443,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,sK0)
        | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) )
    | ~ spl7_9
    | ~ spl7_64 ),
    inference(resolution,[],[f436,f121])).

fof(f436,plain,
    ( ! [X4,X2,X3] :
        ( ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,X4)
        | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) )
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f435])).

fof(f467,plain,
    ( spl7_68
    | ~ spl7_1
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f372,f369,f88,f465])).

fof(f88,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f369,plain,
    ( spl7_56
  <=> ! [X1,X3,X0,X2,X4,X6] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f372,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) )
    | ~ spl7_1
    | ~ spl7_56 ),
    inference(resolution,[],[f370,f89])).

fof(f89,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f370,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( ~ v1_funct_1(X4)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f369])).

fof(f437,plain,
    ( spl7_64
    | ~ spl7_23
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f278,f273,f176,f435])).

fof(f273,plain,
    ( spl7_41
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f278,plain,
    ( ! [X4,X2,X3] :
        ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(X3,X4)
        | ~ l1_pre_topc(X4) )
    | ~ spl7_23
    | ~ spl7_41 ),
    inference(resolution,[],[f274,f177])).

fof(f274,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f273])).

fof(f429,plain,
    ( spl7_63
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f304,f282,f120,f116,f427])).

fof(f282,plain,
    ( spl7_42
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,X2)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f304,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X3,X2)
        | r1_tarski(u1_struct_0(X3),u1_struct_0(X2)) )
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f301,f117])).

fof(f301,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X3,X2)
        | r1_tarski(u1_struct_0(X3),u1_struct_0(X2)) )
    | ~ spl7_9
    | ~ spl7_42 ),
    inference(resolution,[],[f283,f121])).

fof(f283,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,X2)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) )
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f282])).

fof(f371,plain,
    ( spl7_56
    | ~ spl7_33
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f360,f357,f225,f369])).

fof(f225,plain,
    ( spl7_33
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X1)
        | m1_pre_topc(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f357,plain,
    ( spl7_53
  <=> ! [X1,X3,X0,X2,X4,X6] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f360,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl7_33
    | ~ spl7_53 ),
    inference(subsumption_resolution,[],[f358,f226])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f225])).

fof(f358,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f357])).

fof(f359,plain,(
    spl7_53 ),
    inference(avatar_split_clause,[],[f79,f357])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f324,plain,(
    spl7_47 ),
    inference(avatar_split_clause,[],[f69,f322])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f312,plain,(
    spl7_46 ),
    inference(avatar_split_clause,[],[f75,f310])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f284,plain,(
    spl7_42 ),
    inference(avatar_split_clause,[],[f84,f282])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f74,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f275,plain,
    ( spl7_41
    | ~ spl7_23
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f243,f240,f176,f273])).

fof(f240,plain,
    ( spl7_36
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl7_23
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f241,f177])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f240])).

fof(f249,plain,(
    spl7_37 ),
    inference(avatar_split_clause,[],[f85,f247])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f80,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f242,plain,(
    spl7_36 ),
    inference(avatar_split_clause,[],[f63,f240])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f227,plain,(
    spl7_33 ),
    inference(avatar_split_clause,[],[f73,f225])).

fof(f216,plain,
    ( spl7_31
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f203,f193,f156,f108,f214])).

fof(f156,plain,
    ( spl7_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f203,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_27 ),
    inference(backward_demodulation,[],[f157,f200])).

fof(f200,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(resolution,[],[f194,f109])).

fof(f157,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f212,plain,
    ( spl7_30
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f200,f193,f108,f210])).

fof(f208,plain,
    ( spl7_29
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f204,f193,f148,f108,f206])).

fof(f148,plain,
    ( spl7_16
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f204,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_27 ),
    inference(backward_demodulation,[],[f149,f200])).

fof(f149,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f199,plain,(
    spl7_28 ),
    inference(avatar_split_clause,[],[f66,f197])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f195,plain,
    ( spl7_27
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f183,f172,f164,f193])).

fof(f164,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f172,plain,
    ( spl7_22
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f183,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(resolution,[],[f173,f165])).

fof(f165,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f164])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f187,plain,(
    spl7_25 ),
    inference(avatar_split_clause,[],[f72,f185])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f182,plain,(
    spl7_24 ),
    inference(avatar_split_clause,[],[f71,f180])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f178,plain,(
    spl7_23 ),
    inference(avatar_split_clause,[],[f64,f176])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f174,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f59,f172])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f170,plain,(
    spl7_21 ),
    inference(avatar_split_clause,[],[f61,f168])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f166,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f60,f164])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f162,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f82,f160])).

fof(f82,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f42,f41])).

fof(f41,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f42,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f158,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f47,f156])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f154,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f48,f152])).

fof(f48,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f150,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f46,f148])).

fof(f46,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f146,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f43,f144])).

fof(f43,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f142,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f83,f140])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f40,f41])).

fof(f40,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f138,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f44,f136])).

fof(f44,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f134,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f52,f132])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f130,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f50,f128])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f122,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f58,f120])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f118,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f57,f116])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f114,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f56,f112])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f55,f108])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f54,f104])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f53,f100])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f51,f96])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f49,f92])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (19040)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (19032)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (19036)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (19045)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (19031)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (19044)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (19049)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (19035)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (19033)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (19038)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (19048)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (19046)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (19034)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (19041)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (19047)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (19039)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (19050)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (19051)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (19043)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (19037)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (19042)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.36/0.53  % (19040)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.50/0.54  % SZS output start Proof for theBenchmark
% 1.50/0.54  fof(f1537,plain,(
% 1.50/0.54    $false),
% 1.50/0.54    inference(avatar_sat_refutation,[],[f90,f94,f98,f102,f106,f110,f114,f118,f122,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f178,f182,f187,f195,f199,f208,f212,f216,f227,f242,f249,f275,f284,f312,f324,f359,f371,f429,f437,f467,f509,f525,f547,f562,f591,f617,f643,f647,f671,f675,f913,f1045,f1069,f1100,f1122,f1163,f1172,f1175,f1292,f1427,f1510,f1536])).
% 1.50/0.54  fof(f1536,plain,(
% 1.50/0.54    ~spl7_81 | ~spl7_183 | ~spl7_162 | spl7_3 | ~spl7_21 | ~spl7_24 | ~spl7_194),
% 1.50/0.54    inference(avatar_split_clause,[],[f1518,f1508,f180,f168,f96,f1265,f1408,f576])).
% 1.50/0.54  fof(f576,plain,(
% 1.50/0.54    spl7_81 <=> l1_pre_topc(sK2)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).
% 1.50/0.54  fof(f1408,plain,(
% 1.50/0.54    spl7_183 <=> v2_pre_topc(sK2)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).
% 1.50/0.54  fof(f1265,plain,(
% 1.50/0.54    spl7_162 <=> m1_pre_topc(sK3,sK2)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).
% 1.50/0.54  fof(f96,plain,(
% 1.50/0.54    spl7_3 <=> v2_struct_0(sK2)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.50/0.54  fof(f168,plain,(
% 1.50/0.54    spl7_21 <=> ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.50/0.54  fof(f180,plain,(
% 1.50/0.54    spl7_24 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.50/0.54  fof(f1508,plain,(
% 1.50/0.54    spl7_194 <=> ! [X2] : (~v3_pre_topc(k2_struct_0(sK2),X2) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_194])])).
% 1.50/0.54  fof(f1518,plain,(
% 1.50/0.54    ~m1_pre_topc(sK3,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | (spl7_3 | ~spl7_21 | ~spl7_24 | ~spl7_194)),
% 1.50/0.54    inference(subsumption_resolution,[],[f1517,f169])).
% 1.50/0.54  fof(f169,plain,(
% 1.50/0.54    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) ) | ~spl7_21),
% 1.50/0.54    inference(avatar_component_clause,[],[f168])).
% 1.50/0.54  fof(f1517,plain,(
% 1.50/0.54    ~m1_pre_topc(sK3,sK2) | ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | (spl7_3 | ~spl7_24 | ~spl7_194)),
% 1.50/0.54    inference(subsumption_resolution,[],[f1516,f97])).
% 1.50/0.54  fof(f97,plain,(
% 1.50/0.54    ~v2_struct_0(sK2) | spl7_3),
% 1.50/0.54    inference(avatar_component_clause,[],[f96])).
% 1.50/0.54  fof(f1516,plain,(
% 1.50/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | (~spl7_24 | ~spl7_194)),
% 1.50/0.54    inference(duplicate_literal_removal,[],[f1515])).
% 1.50/0.54  fof(f1515,plain,(
% 1.50/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_24 | ~spl7_194)),
% 1.50/0.54    inference(resolution,[],[f1509,f181])).
% 1.50/0.54  fof(f181,plain,(
% 1.50/0.54    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_24),
% 1.50/0.54    inference(avatar_component_clause,[],[f180])).
% 1.50/0.54  fof(f1509,plain,(
% 1.50/0.54    ( ! [X2] : (~v3_pre_topc(k2_struct_0(sK2),X2) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2)) ) | ~spl7_194),
% 1.50/0.54    inference(avatar_component_clause,[],[f1508])).
% 1.50/0.54  fof(f1510,plain,(
% 1.50/0.54    spl7_194 | ~spl7_37 | ~spl7_92 | ~spl7_150),
% 1.50/0.54    inference(avatar_split_clause,[],[f1184,f1169,f673,f247,f1508])).
% 1.50/0.54  fof(f247,plain,(
% 1.50/0.54    spl7_37 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 1.50/0.54  fof(f673,plain,(
% 1.50/0.54    spl7_92 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 1.50/0.54  fof(f1169,plain,(
% 1.50/0.54    spl7_150 <=> ! [X0] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0) | ~l1_pre_topc(X0))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).
% 1.50/0.54  fof(f1184,plain,(
% 1.50/0.54    ( ! [X2] : (~v3_pre_topc(k2_struct_0(sK2),X2) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2)) ) | (~spl7_37 | ~spl7_92 | ~spl7_150)),
% 1.50/0.54    inference(forward_demodulation,[],[f1178,f674])).
% 1.50/0.54  fof(f674,plain,(
% 1.50/0.54    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_92),
% 1.50/0.54    inference(avatar_component_clause,[],[f673])).
% 1.50/0.54  fof(f1178,plain,(
% 1.50/0.54    ( ! [X2] : (v2_struct_0(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v3_pre_topc(u1_struct_0(sK2),X2)) ) | (~spl7_37 | ~spl7_150)),
% 1.50/0.54    inference(duplicate_literal_removal,[],[f1177])).
% 1.50/0.54  fof(f1177,plain,(
% 1.50/0.54    ( ! [X2] : (v2_struct_0(X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK2,X2) | ~v3_pre_topc(u1_struct_0(sK2),X2) | ~v2_pre_topc(X2)) ) | (~spl7_37 | ~spl7_150)),
% 1.50/0.54    inference(resolution,[],[f1170,f248])).
% 1.50/0.54  fof(f248,plain,(
% 1.50/0.54    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0)) ) | ~spl7_37),
% 1.50/0.54    inference(avatar_component_clause,[],[f247])).
% 1.50/0.54  fof(f1170,plain,(
% 1.50/0.54    ( ! [X0] : (~v1_tsep_1(sK2,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_150),
% 1.50/0.54    inference(avatar_component_clause,[],[f1169])).
% 1.50/0.54  fof(f1427,plain,(
% 1.50/0.54    ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_25 | spl7_183),
% 1.50/0.54    inference(avatar_contradiction_clause,[],[f1425])).
% 1.50/0.54  fof(f1425,plain,(
% 1.50/0.54    $false | (~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_25 | spl7_183)),
% 1.50/0.54    inference(unit_resulting_resolution,[],[f117,f121,f133,f1409,f186])).
% 1.50/0.54  fof(f186,plain,(
% 1.50/0.54    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) ) | ~spl7_25),
% 1.50/0.54    inference(avatar_component_clause,[],[f185])).
% 1.50/0.54  fof(f185,plain,(
% 1.50/0.54    spl7_25 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.50/0.54  fof(f1409,plain,(
% 1.50/0.54    ~v2_pre_topc(sK2) | spl7_183),
% 1.50/0.54    inference(avatar_component_clause,[],[f1408])).
% 1.50/0.54  fof(f133,plain,(
% 1.50/0.54    m1_pre_topc(sK2,sK0) | ~spl7_12),
% 1.50/0.54    inference(avatar_component_clause,[],[f132])).
% 1.50/0.54  fof(f132,plain,(
% 1.50/0.54    spl7_12 <=> m1_pre_topc(sK2,sK0)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.50/0.54  fof(f121,plain,(
% 1.50/0.54    l1_pre_topc(sK0) | ~spl7_9),
% 1.50/0.54    inference(avatar_component_clause,[],[f120])).
% 1.50/0.54  fof(f120,plain,(
% 1.50/0.54    spl7_9 <=> l1_pre_topc(sK0)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.50/0.54  fof(f117,plain,(
% 1.50/0.54    v2_pre_topc(sK0) | ~spl7_8),
% 1.50/0.54    inference(avatar_component_clause,[],[f116])).
% 1.50/0.54  fof(f116,plain,(
% 1.50/0.54    spl7_8 <=> v2_pre_topc(sK0)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.50/0.54  fof(f1292,plain,(
% 1.50/0.54    ~spl7_81 | ~spl7_144 | ~spl7_28 | ~spl7_91 | ~spl7_92 | spl7_162),
% 1.50/0.54    inference(avatar_split_clause,[],[f1287,f1265,f673,f669,f197,f1136,f576])).
% 1.50/0.54  fof(f1136,plain,(
% 1.50/0.54    spl7_144 <=> m1_pre_topc(sK3,sK3)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).
% 1.50/0.54  fof(f197,plain,(
% 1.50/0.54    spl7_28 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.50/0.54  fof(f669,plain,(
% 1.50/0.54    spl7_91 <=> sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).
% 1.50/0.54  fof(f1287,plain,(
% 1.50/0.54    ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK2) | (~spl7_28 | ~spl7_91 | ~spl7_92 | spl7_162)),
% 1.50/0.54    inference(forward_demodulation,[],[f1286,f670])).
% 1.50/0.54  fof(f670,plain,(
% 1.50/0.54    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) | ~spl7_91),
% 1.50/0.54    inference(avatar_component_clause,[],[f669])).
% 1.50/0.54  fof(f1286,plain,(
% 1.50/0.54    ~m1_pre_topc(sK3,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | (~spl7_28 | ~spl7_92 | spl7_162)),
% 1.50/0.54    inference(forward_demodulation,[],[f1283,f674])).
% 1.50/0.54  fof(f1283,plain,(
% 1.50/0.54    ~m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | (~spl7_28 | spl7_162)),
% 1.50/0.54    inference(resolution,[],[f1266,f198])).
% 1.50/0.54  fof(f198,plain,(
% 1.50/0.54    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) ) | ~spl7_28),
% 1.50/0.54    inference(avatar_component_clause,[],[f197])).
% 1.50/0.54  fof(f1266,plain,(
% 1.50/0.54    ~m1_pre_topc(sK3,sK2) | spl7_162),
% 1.50/0.54    inference(avatar_component_clause,[],[f1265])).
% 1.50/0.54  fof(f1175,plain,(
% 1.50/0.54    ~spl7_9 | ~spl7_11 | ~spl7_23 | spl7_148),
% 1.50/0.54    inference(avatar_contradiction_clause,[],[f1173])).
% 1.50/0.54  fof(f1173,plain,(
% 1.50/0.54    $false | (~spl7_9 | ~spl7_11 | ~spl7_23 | spl7_148)),
% 1.50/0.54    inference(unit_resulting_resolution,[],[f121,f129,f1162,f177])).
% 1.50/0.54  fof(f177,plain,(
% 1.50/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl7_23),
% 1.50/0.54    inference(avatar_component_clause,[],[f176])).
% 1.50/0.54  fof(f176,plain,(
% 1.50/0.54    spl7_23 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.50/0.54  fof(f1162,plain,(
% 1.50/0.54    ~l1_pre_topc(sK3) | spl7_148),
% 1.50/0.54    inference(avatar_component_clause,[],[f1161])).
% 1.50/0.54  fof(f1161,plain,(
% 1.50/0.54    spl7_148 <=> l1_pre_topc(sK3)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).
% 1.50/0.54  fof(f129,plain,(
% 1.50/0.54    m1_pre_topc(sK3,sK0) | ~spl7_11),
% 1.50/0.54    inference(avatar_component_clause,[],[f128])).
% 1.50/0.54  fof(f128,plain,(
% 1.50/0.54    spl7_11 <=> m1_pre_topc(sK3,sK0)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.50/0.54  fof(f1172,plain,(
% 1.50/0.54    spl7_150 | ~spl7_142 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_88 | ~spl7_92 | ~spl7_120),
% 1.50/0.54    inference(avatar_split_clause,[],[f930,f911,f673,f641,f160,f128,f120,f116,f112,f96,f1120,f1169])).
% 1.50/0.54  fof(f1120,plain,(
% 1.50/0.54    spl7_142 <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).
% 1.50/0.54  fof(f112,plain,(
% 1.50/0.54    spl7_7 <=> v2_struct_0(sK0)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.50/0.54  fof(f160,plain,(
% 1.50/0.54    spl7_19 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.50/0.54  fof(f641,plain,(
% 1.50/0.54    spl7_88 <=> m1_subset_1(sK5,k2_struct_0(sK2))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).
% 1.50/0.54  fof(f911,plain,(
% 1.50/0.54    spl7_120 <=> ! [X1,X0,X2] : (~r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X2))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).
% 1.50/0.54  fof(f930,plain,(
% 1.50/0.54    ( ! [X0] : (~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_88 | ~spl7_92 | ~spl7_120)),
% 1.50/0.54    inference(forward_demodulation,[],[f929,f674])).
% 1.50/0.54  fof(f929,plain,(
% 1.50/0.54    ( ! [X0] : (~r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_88 | ~spl7_92 | ~spl7_120)),
% 1.50/0.54    inference(subsumption_resolution,[],[f928,f642])).
% 1.50/0.54  fof(f642,plain,(
% 1.50/0.54    m1_subset_1(sK5,k2_struct_0(sK2)) | ~spl7_88),
% 1.50/0.54    inference(avatar_component_clause,[],[f641])).
% 1.50/0.54  fof(f928,plain,(
% 1.50/0.54    ( ! [X0] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_92 | ~spl7_120)),
% 1.50/0.54    inference(forward_demodulation,[],[f927,f674])).
% 1.50/0.54  fof(f927,plain,(
% 1.50/0.54    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_120)),
% 1.50/0.54    inference(subsumption_resolution,[],[f926,f117])).
% 1.50/0.54  fof(f926,plain,(
% 1.50/0.54    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(sK0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (spl7_3 | spl7_7 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_120)),
% 1.50/0.54    inference(subsumption_resolution,[],[f925,f121])).
% 1.50/0.54  fof(f925,plain,(
% 1.50/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(sK0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (spl7_3 | spl7_7 | ~spl7_11 | ~spl7_19 | ~spl7_120)),
% 1.50/0.54    inference(subsumption_resolution,[],[f924,f113])).
% 1.50/0.54  fof(f113,plain,(
% 1.50/0.54    ~v2_struct_0(sK0) | spl7_7),
% 1.50/0.54    inference(avatar_component_clause,[],[f112])).
% 1.50/0.54  fof(f924,plain,(
% 1.50/0.54    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(sK0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (spl7_3 | ~spl7_11 | ~spl7_19 | ~spl7_120)),
% 1.50/0.54    inference(subsumption_resolution,[],[f923,f129])).
% 1.50/0.54  fof(f923,plain,(
% 1.50/0.54    ( ! [X0] : (~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(sK0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (spl7_3 | ~spl7_19 | ~spl7_120)),
% 1.50/0.54    inference(subsumption_resolution,[],[f918,f97])).
% 1.50/0.54  fof(f918,plain,(
% 1.50/0.54    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) | ~v2_pre_topc(sK0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0)) ) | (~spl7_19 | ~spl7_120)),
% 1.50/0.54    inference(resolution,[],[f912,f161])).
% 1.50/0.54  fof(f161,plain,(
% 1.50/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl7_19),
% 1.50/0.54    inference(avatar_component_clause,[],[f160])).
% 1.50/0.54  fof(f912,plain,(
% 1.50/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) | ~v2_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X2)) ) | ~spl7_120),
% 1.50/0.54    inference(avatar_component_clause,[],[f911])).
% 1.50/0.54  fof(f1163,plain,(
% 1.50/0.54    ~spl7_148 | ~spl7_21 | spl7_144),
% 1.50/0.54    inference(avatar_split_clause,[],[f1150,f1136,f168,f1161])).
% 1.50/0.54  fof(f1150,plain,(
% 1.50/0.54    ~l1_pre_topc(sK3) | (~spl7_21 | spl7_144)),
% 1.50/0.54    inference(resolution,[],[f1137,f169])).
% 1.50/0.54  fof(f1137,plain,(
% 1.50/0.54    ~m1_pre_topc(sK3,sK3) | spl7_144),
% 1.50/0.54    inference(avatar_component_clause,[],[f1136])).
% 1.50/0.54  fof(f1122,plain,(
% 1.50/0.54    ~spl7_133 | spl7_142 | ~spl7_92 | ~spl7_139),
% 1.50/0.54    inference(avatar_split_clause,[],[f1113,f1098,f673,f1120,f1029])).
% 1.50/0.54  fof(f1029,plain,(
% 1.50/0.54    spl7_133 <=> m1_pre_topc(sK2,sK3)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).
% 1.50/0.54  fof(f1098,plain,(
% 1.50/0.54    spl7_139 <=> ! [X4] : (r1_tarski(u1_struct_0(X4),k2_struct_0(sK3)) | ~m1_pre_topc(X4,sK3))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).
% 1.50/0.54  fof(f1113,plain,(
% 1.50/0.54    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | (~spl7_92 | ~spl7_139)),
% 1.50/0.54    inference(superposition,[],[f1099,f674])).
% 1.50/0.54  fof(f1099,plain,(
% 1.50/0.54    ( ! [X4] : (r1_tarski(u1_struct_0(X4),k2_struct_0(sK3)) | ~m1_pre_topc(X4,sK3)) ) | ~spl7_139),
% 1.50/0.54    inference(avatar_component_clause,[],[f1098])).
% 1.50/0.54  fof(f1100,plain,(
% 1.50/0.54    spl7_139 | ~spl7_11 | ~spl7_63 | ~spl7_89),
% 1.50/0.54    inference(avatar_split_clause,[],[f666,f645,f427,f128,f1098])).
% 1.50/0.54  fof(f427,plain,(
% 1.50/0.54    spl7_63 <=> ! [X3,X2] : (~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,X2) | r1_tarski(u1_struct_0(X3),u1_struct_0(X2)))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 1.50/0.54  fof(f645,plain,(
% 1.50/0.54    spl7_89 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).
% 1.50/0.54  fof(f666,plain,(
% 1.50/0.54    ( ! [X4] : (r1_tarski(u1_struct_0(X4),k2_struct_0(sK3)) | ~m1_pre_topc(X4,sK3)) ) | (~spl7_11 | ~spl7_63 | ~spl7_89)),
% 1.50/0.54    inference(subsumption_resolution,[],[f658,f129])).
% 1.50/0.54  fof(f658,plain,(
% 1.50/0.54    ( ! [X4] : (r1_tarski(u1_struct_0(X4),k2_struct_0(sK3)) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(sK3,sK0)) ) | (~spl7_63 | ~spl7_89)),
% 1.50/0.54    inference(superposition,[],[f428,f646])).
% 1.50/0.54  fof(f646,plain,(
% 1.50/0.54    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl7_89),
% 1.50/0.54    inference(avatar_component_clause,[],[f645])).
% 1.50/0.54  fof(f428,plain,(
% 1.50/0.54    ( ! [X2,X3] : (r1_tarski(u1_struct_0(X3),u1_struct_0(X2)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X2,sK0)) ) | ~spl7_63),
% 1.50/0.54    inference(avatar_component_clause,[],[f427])).
% 1.50/0.54  fof(f1069,plain,(
% 1.50/0.54    ~spl7_81 | ~spl7_21 | spl7_135),
% 1.50/0.54    inference(avatar_split_clause,[],[f1059,f1043,f168,f576])).
% 1.50/0.54  fof(f1043,plain,(
% 1.50/0.54    spl7_135 <=> m1_pre_topc(sK2,sK2)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).
% 1.50/0.54  fof(f1059,plain,(
% 1.50/0.54    ~l1_pre_topc(sK2) | (~spl7_21 | spl7_135)),
% 1.50/0.54    inference(resolution,[],[f1044,f169])).
% 1.50/0.54  fof(f1044,plain,(
% 1.50/0.54    ~m1_pre_topc(sK2,sK2) | spl7_135),
% 1.50/0.54    inference(avatar_component_clause,[],[f1043])).
% 1.50/0.54  fof(f1045,plain,(
% 1.50/0.54    ~spl7_135 | ~spl7_75 | spl7_133),
% 1.50/0.54    inference(avatar_split_clause,[],[f1035,f1029,f523,f1043])).
% 1.50/0.54  fof(f523,plain,(
% 1.50/0.54    spl7_75 <=> ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 1.50/0.54  fof(f1035,plain,(
% 1.50/0.54    ~m1_pre_topc(sK2,sK2) | (~spl7_75 | spl7_133)),
% 1.50/0.54    inference(resolution,[],[f1030,f524])).
% 1.50/0.54  fof(f524,plain,(
% 1.50/0.54    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2)) ) | ~spl7_75),
% 1.50/0.54    inference(avatar_component_clause,[],[f523])).
% 1.50/0.54  fof(f1030,plain,(
% 1.50/0.54    ~m1_pre_topc(sK2,sK3) | spl7_133),
% 1.50/0.54    inference(avatar_component_clause,[],[f1029])).
% 1.50/0.54  fof(f913,plain,(
% 1.50/0.54    spl7_120 | spl7_2 | ~spl7_11 | ~spl7_46 | ~spl7_47 | ~spl7_80 | ~spl7_86),
% 1.50/0.54    inference(avatar_split_clause,[],[f628,f615,f560,f322,f310,f128,f92,f911])).
% 1.50/0.54  fof(f92,plain,(
% 1.50/0.54    spl7_2 <=> v2_struct_0(sK3)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.50/0.54  fof(f310,plain,(
% 1.50/0.54    spl7_46 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 1.50/0.54  fof(f322,plain,(
% 1.50/0.54    spl7_47 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 1.50/0.54  fof(f560,plain,(
% 1.50/0.54    spl7_80 <=> ! [X1,X0] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).
% 1.50/0.54  fof(f615,plain,(
% 1.50/0.54    spl7_86 <=> ! [X1] : (~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = k2_struct_0(X1))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).
% 1.50/0.54  fof(f628,plain,(
% 1.50/0.54    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X2)) ) | (spl7_2 | ~spl7_11 | ~spl7_46 | ~spl7_47 | ~spl7_80 | ~spl7_86)),
% 1.50/0.54    inference(backward_demodulation,[],[f572,f618])).
% 1.50/0.54  fof(f618,plain,(
% 1.50/0.54    u1_struct_0(sK3) = k2_struct_0(sK3) | (~spl7_11 | ~spl7_86)),
% 1.50/0.54    inference(resolution,[],[f616,f129])).
% 1.50/0.54  fof(f616,plain,(
% 1.50/0.54    ( ! [X1] : (~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = k2_struct_0(X1)) ) | ~spl7_86),
% 1.50/0.54    inference(avatar_component_clause,[],[f615])).
% 1.50/0.54  fof(f572,plain,(
% 1.50/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(sK3,X2) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) | v2_struct_0(X2)) ) | (spl7_2 | ~spl7_46 | ~spl7_47 | ~spl7_80)),
% 1.50/0.54    inference(subsumption_resolution,[],[f571,f311])).
% 1.50/0.54  fof(f311,plain,(
% 1.50/0.54    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) ) | ~spl7_46),
% 1.50/0.54    inference(avatar_component_clause,[],[f310])).
% 1.50/0.54  fof(f571,plain,(
% 1.50/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(sK3,X2) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) | v2_struct_0(X2)) ) | (spl7_2 | ~spl7_47 | ~spl7_80)),
% 1.50/0.54    inference(subsumption_resolution,[],[f568,f93])).
% 1.50/0.54  fof(f93,plain,(
% 1.50/0.54    ~v2_struct_0(sK3) | spl7_2),
% 1.50/0.54    inference(avatar_component_clause,[],[f92])).
% 1.50/0.54  fof(f568,plain,(
% 1.50/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X2) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) | v2_struct_0(X2)) ) | (~spl7_47 | ~spl7_80)),
% 1.50/0.54    inference(resolution,[],[f561,f323])).
% 1.50/0.54  fof(f323,plain,(
% 1.50/0.54    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v2_struct_0(X0)) ) | ~spl7_47),
% 1.50/0.54    inference(avatar_component_clause,[],[f322])).
% 1.50/0.54  fof(f561,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~v1_tsep_1(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | ~spl7_80),
% 1.50/0.54    inference(avatar_component_clause,[],[f560])).
% 1.50/0.54  fof(f675,plain,(
% 1.50/0.54    spl7_92 | ~spl7_12 | ~spl7_86),
% 1.50/0.54    inference(avatar_split_clause,[],[f619,f615,f132,f673])).
% 1.50/0.54  fof(f619,plain,(
% 1.50/0.54    u1_struct_0(sK2) = k2_struct_0(sK2) | (~spl7_12 | ~spl7_86)),
% 1.50/0.54    inference(resolution,[],[f616,f133])).
% 1.50/0.54  fof(f671,plain,(
% 1.50/0.54    spl7_91 | ~spl7_12 | ~spl7_17 | ~spl7_86),
% 1.50/0.54    inference(avatar_split_clause,[],[f632,f615,f152,f132,f669])).
% 1.50/0.54  fof(f152,plain,(
% 1.50/0.54    spl7_17 <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.50/0.54  fof(f632,plain,(
% 1.50/0.54    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) | (~spl7_12 | ~spl7_17 | ~spl7_86)),
% 1.50/0.54    inference(backward_demodulation,[],[f153,f619])).
% 1.50/0.54  fof(f153,plain,(
% 1.50/0.54    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl7_17),
% 1.50/0.54    inference(avatar_component_clause,[],[f152])).
% 1.50/0.54  fof(f647,plain,(
% 1.50/0.54    spl7_89 | ~spl7_11 | ~spl7_86),
% 1.50/0.54    inference(avatar_split_clause,[],[f618,f615,f128,f645])).
% 1.50/0.54  fof(f643,plain,(
% 1.50/0.54    spl7_88 | ~spl7_12 | ~spl7_14 | ~spl7_86),
% 1.50/0.54    inference(avatar_split_clause,[],[f633,f615,f140,f132,f641])).
% 1.50/0.54  fof(f140,plain,(
% 1.50/0.54    spl7_14 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.50/0.54  fof(f633,plain,(
% 1.50/0.54    m1_subset_1(sK5,k2_struct_0(sK2)) | (~spl7_12 | ~spl7_14 | ~spl7_86)),
% 1.50/0.54    inference(backward_demodulation,[],[f141,f619])).
% 1.50/0.54  fof(f141,plain,(
% 1.50/0.54    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_14),
% 1.50/0.54    inference(avatar_component_clause,[],[f140])).
% 1.50/0.54  fof(f617,plain,(
% 1.50/0.54    spl7_86 | ~spl7_9 | ~spl7_79),
% 1.50/0.54    inference(avatar_split_clause,[],[f557,f545,f120,f615])).
% 1.50/0.54  fof(f545,plain,(
% 1.50/0.54    spl7_79 <=> ! [X1,X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).
% 1.50/0.54  fof(f557,plain,(
% 1.50/0.54    ( ! [X1] : (~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = k2_struct_0(X1)) ) | (~spl7_9 | ~spl7_79)),
% 1.50/0.54    inference(resolution,[],[f546,f121])).
% 1.50/0.54  fof(f546,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl7_79),
% 1.50/0.54    inference(avatar_component_clause,[],[f545])).
% 1.50/0.54  fof(f591,plain,(
% 1.50/0.54    ~spl7_9 | ~spl7_12 | ~spl7_23 | spl7_81),
% 1.50/0.54    inference(avatar_contradiction_clause,[],[f589])).
% 1.50/0.54  fof(f589,plain,(
% 1.50/0.54    $false | (~spl7_9 | ~spl7_12 | ~spl7_23 | spl7_81)),
% 1.50/0.54    inference(unit_resulting_resolution,[],[f121,f133,f577,f177])).
% 1.50/0.54  fof(f577,plain,(
% 1.50/0.54    ~l1_pre_topc(sK2) | spl7_81),
% 1.50/0.54    inference(avatar_component_clause,[],[f576])).
% 1.50/0.54  fof(f562,plain,(
% 1.50/0.54    spl7_80 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_29 | ~spl7_30 | ~spl7_31 | ~spl7_68),
% 1.50/0.54    inference(avatar_split_clause,[],[f479,f465,f214,f210,f206,f144,f136,f108,f104,f100,f92,f560])).
% 1.50/0.54  fof(f100,plain,(
% 1.50/0.54    spl7_4 <=> v2_struct_0(sK1)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.50/0.54  fof(f104,plain,(
% 1.50/0.54    spl7_5 <=> v2_pre_topc(sK1)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.50/0.54  fof(f108,plain,(
% 1.50/0.54    spl7_6 <=> l1_pre_topc(sK1)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.50/0.54  fof(f136,plain,(
% 1.50/0.54    spl7_13 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.50/0.54  fof(f144,plain,(
% 1.50/0.54    spl7_15 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.50/0.54  fof(f206,plain,(
% 1.50/0.54    spl7_29 <=> v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 1.50/0.54  fof(f210,plain,(
% 1.50/0.54    spl7_30 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 1.50/0.54  fof(f214,plain,(
% 1.50/0.54    spl7_31 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.50/0.54  fof(f465,plain,(
% 1.50/0.54    spl7_68 <=> ! [X1,X3,X0,X2,X4] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 1.50/0.54  fof(f479,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_29 | ~spl7_30 | ~spl7_31 | ~spl7_68)),
% 1.50/0.54    inference(subsumption_resolution,[],[f478,f215])).
% 1.50/0.54  fof(f215,plain,(
% 1.50/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | ~spl7_31),
% 1.50/0.54    inference(avatar_component_clause,[],[f214])).
% 1.50/0.54  fof(f478,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_29 | ~spl7_30 | ~spl7_68)),
% 1.50/0.54    inference(forward_demodulation,[],[f477,f211])).
% 1.50/0.54  fof(f211,plain,(
% 1.50/0.54    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl7_30),
% 1.50/0.54    inference(avatar_component_clause,[],[f210])).
% 1.50/0.54  fof(f477,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_29 | ~spl7_30 | ~spl7_68)),
% 1.50/0.54    inference(subsumption_resolution,[],[f476,f207])).
% 1.50/0.54  fof(f207,plain,(
% 1.50/0.54    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | ~spl7_29),
% 1.50/0.54    inference(avatar_component_clause,[],[f206])).
% 1.50/0.54  fof(f476,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_30 | ~spl7_68)),
% 1.50/0.54    inference(forward_demodulation,[],[f475,f211])).
% 1.50/0.54  fof(f475,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_68)),
% 1.50/0.54    inference(subsumption_resolution,[],[f474,f137])).
% 1.50/0.54  fof(f137,plain,(
% 1.50/0.54    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_13),
% 1.50/0.54    inference(avatar_component_clause,[],[f136])).
% 1.50/0.54  fof(f474,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_68)),
% 1.50/0.54    inference(subsumption_resolution,[],[f473,f93])).
% 1.50/0.54  fof(f473,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_68)),
% 1.50/0.54    inference(subsumption_resolution,[],[f472,f109])).
% 1.50/0.54  fof(f109,plain,(
% 1.50/0.54    l1_pre_topc(sK1) | ~spl7_6),
% 1.50/0.54    inference(avatar_component_clause,[],[f108])).
% 1.50/0.54  fof(f472,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_4 | ~spl7_5 | spl7_15 | ~spl7_68)),
% 1.50/0.54    inference(subsumption_resolution,[],[f471,f105])).
% 1.50/0.54  fof(f105,plain,(
% 1.50/0.54    v2_pre_topc(sK1) | ~spl7_5),
% 1.50/0.54    inference(avatar_component_clause,[],[f104])).
% 1.50/0.54  fof(f471,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_4 | spl7_15 | ~spl7_68)),
% 1.50/0.54    inference(subsumption_resolution,[],[f470,f101])).
% 1.50/0.54  fof(f101,plain,(
% 1.50/0.54    ~v2_struct_0(sK1) | spl7_4),
% 1.50/0.54    inference(avatar_component_clause,[],[f100])).
% 1.50/0.54  fof(f470,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (spl7_15 | ~spl7_68)),
% 1.50/0.54    inference(resolution,[],[f466,f145])).
% 1.50/0.54  fof(f145,plain,(
% 1.50/0.54    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl7_15),
% 1.50/0.54    inference(avatar_component_clause,[],[f144])).
% 1.50/0.54  fof(f466,plain,(
% 1.50/0.54    ( ! [X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,sK4,X4) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | ~v2_pre_topc(X0)) ) | ~spl7_68),
% 1.50/0.54    inference(avatar_component_clause,[],[f465])).
% 1.50/0.54  fof(f547,plain,(
% 1.50/0.54    spl7_79 | ~spl7_23 | ~spl7_27),
% 1.50/0.54    inference(avatar_split_clause,[],[f202,f193,f176,f545])).
% 1.50/0.54  fof(f193,plain,(
% 1.50/0.54    spl7_27 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.50/0.54  fof(f202,plain,(
% 1.50/0.54    ( ! [X0,X1] : (k2_struct_0(X0) = u1_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) ) | (~spl7_23 | ~spl7_27)),
% 1.50/0.54    inference(resolution,[],[f194,f177])).
% 1.50/0.54  fof(f194,plain,(
% 1.50/0.54    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl7_27),
% 1.50/0.54    inference(avatar_component_clause,[],[f193])).
% 1.50/0.54  fof(f525,plain,(
% 1.50/0.54    spl7_75 | ~spl7_12 | ~spl7_17 | ~spl7_73),
% 1.50/0.54    inference(avatar_split_clause,[],[f517,f507,f152,f132,f523])).
% 1.50/0.54  fof(f507,plain,(
% 1.50/0.54    spl7_73 <=> ! [X3,X2] : (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 1.50/0.54  fof(f517,plain,(
% 1.50/0.54    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2)) ) | (~spl7_12 | ~spl7_17 | ~spl7_73)),
% 1.50/0.54    inference(subsumption_resolution,[],[f516,f133])).
% 1.50/0.54  fof(f516,plain,(
% 1.50/0.54    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X0,sK2)) ) | (~spl7_17 | ~spl7_73)),
% 1.50/0.54    inference(superposition,[],[f508,f153])).
% 1.50/0.54  fof(f508,plain,(
% 1.50/0.54    ( ! [X2,X3] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,X3)) ) | ~spl7_73),
% 1.50/0.54    inference(avatar_component_clause,[],[f507])).
% 1.50/0.54  fof(f509,plain,(
% 1.50/0.54    spl7_73 | ~spl7_9 | ~spl7_64),
% 1.50/0.54    inference(avatar_split_clause,[],[f443,f435,f120,f507])).
% 1.50/0.54  fof(f435,plain,(
% 1.50/0.54    spl7_64 <=> ! [X3,X2,X4] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X4) | ~l1_pre_topc(X4))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 1.50/0.54  fof(f443,plain,(
% 1.50/0.54    ( ! [X2,X3] : (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))) ) | (~spl7_9 | ~spl7_64)),
% 1.50/0.54    inference(resolution,[],[f436,f121])).
% 1.50/0.54  fof(f436,plain,(
% 1.50/0.54    ( ! [X4,X2,X3] : (~l1_pre_topc(X4) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X4) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))) ) | ~spl7_64),
% 1.50/0.54    inference(avatar_component_clause,[],[f435])).
% 1.50/0.54  fof(f467,plain,(
% 1.50/0.54    spl7_68 | ~spl7_1 | ~spl7_56),
% 1.50/0.54    inference(avatar_split_clause,[],[f372,f369,f88,f465])).
% 1.50/0.54  fof(f88,plain,(
% 1.50/0.54    spl7_1 <=> v1_funct_1(sK4)),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.50/0.54  fof(f369,plain,(
% 1.50/0.54    spl7_56 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 1.50/0.54  fof(f372,plain,(
% 1.50/0.54    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) ) | (~spl7_1 | ~spl7_56)),
% 1.50/0.54    inference(resolution,[],[f370,f89])).
% 1.50/0.54  fof(f89,plain,(
% 1.50/0.54    v1_funct_1(sK4) | ~spl7_1),
% 1.50/0.54    inference(avatar_component_clause,[],[f88])).
% 1.50/0.54  fof(f370,plain,(
% 1.50/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | ~spl7_56),
% 1.50/0.54    inference(avatar_component_clause,[],[f369])).
% 1.50/0.54  fof(f437,plain,(
% 1.50/0.54    spl7_64 | ~spl7_23 | ~spl7_41),
% 1.50/0.54    inference(avatar_split_clause,[],[f278,f273,f176,f435])).
% 1.50/0.54  fof(f273,plain,(
% 1.50/0.54    spl7_41 <=> ! [X1,X0] : (~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 1.50/0.54  fof(f278,plain,(
% 1.50/0.54    ( ! [X4,X2,X3] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X4) | ~l1_pre_topc(X4)) ) | (~spl7_23 | ~spl7_41)),
% 1.50/0.54    inference(resolution,[],[f274,f177])).
% 1.50/0.54  fof(f274,plain,(
% 1.50/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) ) | ~spl7_41),
% 1.50/0.54    inference(avatar_component_clause,[],[f273])).
% 1.50/0.54  fof(f429,plain,(
% 1.50/0.54    spl7_63 | ~spl7_8 | ~spl7_9 | ~spl7_42),
% 1.50/0.54    inference(avatar_split_clause,[],[f304,f282,f120,f116,f427])).
% 1.50/0.54  fof(f282,plain,(
% 1.50/0.54    spl7_42 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 1.50/0.54  fof(f304,plain,(
% 1.50/0.54    ( ! [X2,X3] : (~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,X2) | r1_tarski(u1_struct_0(X3),u1_struct_0(X2))) ) | (~spl7_8 | ~spl7_9 | ~spl7_42)),
% 1.50/0.54    inference(subsumption_resolution,[],[f301,f117])).
% 1.50/0.54  fof(f301,plain,(
% 1.50/0.54    ( ! [X2,X3] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,X2) | r1_tarski(u1_struct_0(X3),u1_struct_0(X2))) ) | (~spl7_9 | ~spl7_42)),
% 1.50/0.54    inference(resolution,[],[f283,f121])).
% 1.50/0.54  fof(f283,plain,(
% 1.50/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) ) | ~spl7_42),
% 1.50/0.54    inference(avatar_component_clause,[],[f282])).
% 1.50/0.54  fof(f371,plain,(
% 1.50/0.54    spl7_56 | ~spl7_33 | ~spl7_53),
% 1.50/0.54    inference(avatar_split_clause,[],[f360,f357,f225,f369])).
% 1.50/0.54  fof(f225,plain,(
% 1.50/0.54    spl7_33 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0))),
% 1.50/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 1.50/0.55  fof(f357,plain,(
% 1.50/0.55    spl7_53 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 1.50/0.55  fof(f360,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | (~spl7_33 | ~spl7_53)),
% 1.50/0.55    inference(subsumption_resolution,[],[f358,f226])).
% 1.50/0.55  fof(f226,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | ~v2_pre_topc(X0)) ) | ~spl7_33),
% 1.50/0.55    inference(avatar_component_clause,[],[f225])).
% 1.50/0.55  fof(f358,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | ~spl7_53),
% 1.50/0.55    inference(avatar_component_clause,[],[f357])).
% 1.50/0.55  fof(f359,plain,(
% 1.50/0.55    spl7_53),
% 1.50/0.55    inference(avatar_split_clause,[],[f79,f357])).
% 1.50/0.55  fof(f79,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) )),
% 1.50/0.55    inference(equality_resolution,[],[f67])).
% 1.50/0.55  fof(f67,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f27])).
% 1.50/0.55  fof(f27,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.55    inference(flattening,[],[f26])).
% 1.50/0.55  fof(f26,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.55    inference(ennf_transformation,[],[f14])).
% 1.50/0.55  fof(f14,axiom,(
% 1.50/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.50/0.55  fof(f324,plain,(
% 1.50/0.55    spl7_47),
% 1.50/0.55    inference(avatar_split_clause,[],[f69,f322])).
% 1.50/0.55  fof(f69,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f29])).
% 1.50/0.55  fof(f29,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.55    inference(flattening,[],[f28])).
% 1.50/0.55  fof(f28,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.55    inference(ennf_transformation,[],[f9])).
% 1.50/0.55  fof(f9,axiom,(
% 1.50/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).
% 1.50/0.55  fof(f312,plain,(
% 1.50/0.55    spl7_46),
% 1.50/0.55    inference(avatar_split_clause,[],[f75,f310])).
% 1.50/0.55  fof(f75,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f37])).
% 1.50/0.55  fof(f37,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.55    inference(flattening,[],[f36])).
% 1.50/0.55  fof(f36,plain,(
% 1.50/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.55    inference(ennf_transformation,[],[f12])).
% 1.50/0.55  fof(f12,axiom,(
% 1.50/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.50/0.56  fof(f284,plain,(
% 1.50/0.56    spl7_42),
% 1.50/0.56    inference(avatar_split_clause,[],[f84,f282])).
% 1.50/0.56  fof(f84,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f74,f73])).
% 1.50/0.56  fof(f73,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f35])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.56    inference(flattening,[],[f34])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f13])).
% 1.50/0.56  fof(f13,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.50/0.56  fof(f74,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f37])).
% 1.50/0.56  fof(f275,plain,(
% 1.50/0.56    spl7_41 | ~spl7_23 | ~spl7_36),
% 1.50/0.56    inference(avatar_split_clause,[],[f243,f240,f176,f273])).
% 1.50/0.56  fof(f240,plain,(
% 1.50/0.56    spl7_36 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 1.50/0.56  fof(f243,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) ) | (~spl7_23 | ~spl7_36)),
% 1.50/0.56    inference(subsumption_resolution,[],[f241,f177])).
% 1.50/0.56  fof(f241,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) ) | ~spl7_36),
% 1.50/0.56    inference(avatar_component_clause,[],[f240])).
% 1.50/0.56  fof(f249,plain,(
% 1.50/0.56    spl7_37),
% 1.50/0.56    inference(avatar_split_clause,[],[f85,f247])).
% 1.50/0.56  fof(f85,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f80,f65])).
% 1.50/0.56  fof(f65,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f24])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.50/0.56  fof(f80,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.50/0.56    inference(equality_resolution,[],[f77])).
% 1.50/0.56  fof(f77,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f39])).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.56    inference(flattening,[],[f38])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f8])).
% 1.50/0.56  fof(f8,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.50/0.56  fof(f242,plain,(
% 1.50/0.56    spl7_36),
% 1.50/0.56    inference(avatar_split_clause,[],[f63,f240])).
% 1.50/0.56  fof(f63,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.50/0.56  fof(f227,plain,(
% 1.50/0.56    spl7_33),
% 1.50/0.56    inference(avatar_split_clause,[],[f73,f225])).
% 1.50/0.56  fof(f216,plain,(
% 1.50/0.56    spl7_31 | ~spl7_6 | ~spl7_18 | ~spl7_27),
% 1.50/0.56    inference(avatar_split_clause,[],[f203,f193,f156,f108,f214])).
% 1.50/0.56  fof(f156,plain,(
% 1.50/0.56    spl7_18 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.50/0.56  fof(f203,plain,(
% 1.50/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | (~spl7_6 | ~spl7_18 | ~spl7_27)),
% 1.50/0.56    inference(backward_demodulation,[],[f157,f200])).
% 1.50/0.56  fof(f200,plain,(
% 1.50/0.56    u1_struct_0(sK1) = k2_struct_0(sK1) | (~spl7_6 | ~spl7_27)),
% 1.50/0.56    inference(resolution,[],[f194,f109])).
% 1.50/0.56  fof(f157,plain,(
% 1.50/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl7_18),
% 1.50/0.56    inference(avatar_component_clause,[],[f156])).
% 1.50/0.56  fof(f212,plain,(
% 1.50/0.56    spl7_30 | ~spl7_6 | ~spl7_27),
% 1.50/0.56    inference(avatar_split_clause,[],[f200,f193,f108,f210])).
% 1.50/0.56  fof(f208,plain,(
% 1.50/0.56    spl7_29 | ~spl7_6 | ~spl7_16 | ~spl7_27),
% 1.50/0.56    inference(avatar_split_clause,[],[f204,f193,f148,f108,f206])).
% 1.50/0.56  fof(f148,plain,(
% 1.50/0.56    spl7_16 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.50/0.56  fof(f204,plain,(
% 1.50/0.56    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | (~spl7_6 | ~spl7_16 | ~spl7_27)),
% 1.50/0.56    inference(backward_demodulation,[],[f149,f200])).
% 1.50/0.56  fof(f149,plain,(
% 1.50/0.56    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl7_16),
% 1.50/0.56    inference(avatar_component_clause,[],[f148])).
% 1.50/0.56  fof(f199,plain,(
% 1.50/0.56    spl7_28),
% 1.50/0.56    inference(avatar_split_clause,[],[f66,f197])).
% 1.50/0.56  fof(f66,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.50/0.56  fof(f195,plain,(
% 1.50/0.56    spl7_27 | ~spl7_20 | ~spl7_22),
% 1.50/0.56    inference(avatar_split_clause,[],[f183,f172,f164,f193])).
% 1.50/0.56  fof(f164,plain,(
% 1.50/0.56    spl7_20 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.50/0.56  fof(f172,plain,(
% 1.50/0.56    spl7_22 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.50/0.56  fof(f183,plain,(
% 1.50/0.56    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl7_20 | ~spl7_22)),
% 1.50/0.56    inference(resolution,[],[f173,f165])).
% 1.50/0.56  fof(f165,plain,(
% 1.50/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl7_20),
% 1.50/0.56    inference(avatar_component_clause,[],[f164])).
% 1.50/0.56  fof(f173,plain,(
% 1.50/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl7_22),
% 1.50/0.56    inference(avatar_component_clause,[],[f172])).
% 1.50/0.56  fof(f187,plain,(
% 1.50/0.56    spl7_25),
% 1.50/0.56    inference(avatar_split_clause,[],[f72,f185])).
% 1.50/0.56  fof(f72,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f33])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.56    inference(flattening,[],[f32])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.50/0.56  fof(f182,plain,(
% 1.50/0.56    spl7_24),
% 1.50/0.56    inference(avatar_split_clause,[],[f71,f180])).
% 1.50/0.56  fof(f71,plain,(
% 1.50/0.56    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.56    inference(flattening,[],[f30])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.50/0.56  fof(f178,plain,(
% 1.50/0.56    spl7_23),
% 1.50/0.56    inference(avatar_split_clause,[],[f64,f176])).
% 1.50/0.56  fof(f64,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.50/0.56  fof(f174,plain,(
% 1.50/0.56    spl7_22),
% 1.50/0.56    inference(avatar_split_clause,[],[f59,f172])).
% 1.50/0.56  fof(f59,plain,(
% 1.50/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.50/0.56  fof(f170,plain,(
% 1.50/0.56    spl7_21),
% 1.50/0.56    inference(avatar_split_clause,[],[f61,f168])).
% 1.50/0.56  fof(f61,plain,(
% 1.50/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f21])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.50/0.56  fof(f166,plain,(
% 1.50/0.56    spl7_20),
% 1.50/0.56    inference(avatar_split_clause,[],[f60,f164])).
% 1.50/0.56  fof(f60,plain,(
% 1.50/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f20])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.50/0.56  fof(f162,plain,(
% 1.50/0.56    spl7_19),
% 1.50/0.56    inference(avatar_split_clause,[],[f82,f160])).
% 1.50/0.56  fof(f82,plain,(
% 1.50/0.56    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.50/0.56    inference(backward_demodulation,[],[f42,f41])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    sK5 = sK6),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f18,plain,(
% 1.50/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.50/0.56    inference(flattening,[],[f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f16])).
% 1.50/0.56  fof(f16,negated_conjecture,(
% 1.50/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.50/0.56    inference(negated_conjecture,[],[f15])).
% 1.50/0.56  fof(f15,conjecture,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.50/0.56  fof(f42,plain,(
% 1.50/0.56    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f158,plain,(
% 1.50/0.56    spl7_18),
% 1.50/0.56    inference(avatar_split_clause,[],[f47,f156])).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f154,plain,(
% 1.50/0.56    spl7_17),
% 1.50/0.56    inference(avatar_split_clause,[],[f48,f152])).
% 1.50/0.56  fof(f48,plain,(
% 1.50/0.56    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f150,plain,(
% 1.50/0.56    spl7_16),
% 1.50/0.56    inference(avatar_split_clause,[],[f46,f148])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f146,plain,(
% 1.50/0.56    ~spl7_15),
% 1.50/0.56    inference(avatar_split_clause,[],[f43,f144])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f142,plain,(
% 1.50/0.56    spl7_14),
% 1.50/0.56    inference(avatar_split_clause,[],[f83,f140])).
% 1.50/0.56  fof(f83,plain,(
% 1.50/0.56    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.50/0.56    inference(forward_demodulation,[],[f40,f41])).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f138,plain,(
% 1.50/0.56    spl7_13),
% 1.50/0.56    inference(avatar_split_clause,[],[f44,f136])).
% 1.50/0.56  fof(f44,plain,(
% 1.50/0.56    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f134,plain,(
% 1.50/0.56    spl7_12),
% 1.50/0.56    inference(avatar_split_clause,[],[f52,f132])).
% 1.50/0.56  fof(f52,plain,(
% 1.50/0.56    m1_pre_topc(sK2,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f130,plain,(
% 1.50/0.56    spl7_11),
% 1.50/0.56    inference(avatar_split_clause,[],[f50,f128])).
% 1.50/0.56  fof(f50,plain,(
% 1.50/0.56    m1_pre_topc(sK3,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f122,plain,(
% 1.50/0.56    spl7_9),
% 1.50/0.56    inference(avatar_split_clause,[],[f58,f120])).
% 1.50/0.56  fof(f58,plain,(
% 1.50/0.56    l1_pre_topc(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f118,plain,(
% 1.50/0.56    spl7_8),
% 1.50/0.56    inference(avatar_split_clause,[],[f57,f116])).
% 1.50/0.56  fof(f57,plain,(
% 1.50/0.56    v2_pre_topc(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f114,plain,(
% 1.50/0.56    ~spl7_7),
% 1.50/0.56    inference(avatar_split_clause,[],[f56,f112])).
% 1.50/0.56  fof(f56,plain,(
% 1.50/0.56    ~v2_struct_0(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f110,plain,(
% 1.50/0.56    spl7_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f55,f108])).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    l1_pre_topc(sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f106,plain,(
% 1.50/0.56    spl7_5),
% 1.50/0.56    inference(avatar_split_clause,[],[f54,f104])).
% 1.50/0.56  fof(f54,plain,(
% 1.50/0.56    v2_pre_topc(sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f102,plain,(
% 1.50/0.56    ~spl7_4),
% 1.50/0.56    inference(avatar_split_clause,[],[f53,f100])).
% 1.50/0.56  fof(f53,plain,(
% 1.50/0.56    ~v2_struct_0(sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f98,plain,(
% 1.50/0.56    ~spl7_3),
% 1.50/0.56    inference(avatar_split_clause,[],[f51,f96])).
% 1.50/0.56  fof(f51,plain,(
% 1.50/0.56    ~v2_struct_0(sK2)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f94,plain,(
% 1.50/0.56    ~spl7_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f49,f92])).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    ~v2_struct_0(sK3)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f90,plain,(
% 1.50/0.56    spl7_1),
% 1.50/0.56    inference(avatar_split_clause,[],[f45,f88])).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    v1_funct_1(sK4)),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (19040)------------------------------
% 1.50/0.56  % (19040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (19040)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (19040)Memory used [KB]: 11641
% 1.50/0.56  % (19040)Time elapsed: 0.124 s
% 1.50/0.56  % (19040)------------------------------
% 1.50/0.56  % (19040)------------------------------
% 1.50/0.56  % (19030)Success in time 0.211 s
%------------------------------------------------------------------------------
