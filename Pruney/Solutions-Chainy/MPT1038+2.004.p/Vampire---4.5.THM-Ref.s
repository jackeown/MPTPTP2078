%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 270 expanded)
%              Number of leaves         :   23 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  518 (1370 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f48,f52,f56,f60,f64,f68,f72,f76,f83,f89,f95,f114,f118,f135,f146,f150])).

fof(f150,plain,
    ( ~ spl4_1
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_18
    | spl4_23 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_18
    | spl4_23 ),
    inference(unit_resulting_resolution,[],[f27,f113,f117,f145,f67])).

fof(f67,plain,
    ( ! [X2,X1] :
        ( v1_partfun1(X2,k1_xboole_0)
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_11
  <=> ! [X1,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_partfun1(X2,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f145,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_23
  <=> v1_partfun1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f113,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_17
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f27,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f146,plain,
    ( ~ spl4_23
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f141,f133,f116,f42,f38,f26,f144])).

fof(f38,plain,
    ( spl4_4
  <=> r1_partfun1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f42,plain,
    ( spl4_5
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f133,plain,
    ( spl4_22
  <=> ! [X0] :
        ( ~ v1_partfun1(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f141,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f140,f27])).

fof(f140,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f139,f39])).

fof(f39,plain,
    ( r1_partfun1(sK1,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f139,plain,
    ( ~ r1_partfun1(sK1,sK3)
    | ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_5
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f136,f117])).

fof(f136,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_partfun1(sK1,sK3)
    | ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(resolution,[],[f134,f43])).

fof(f43,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl4_22
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f108,f93,f87,f54,f50,f42,f38,f26,f133])).

fof(f50,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f54,plain,
    ( spl4_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f87,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_partfun1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f93,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f106,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f55,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f100,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f99,f27])).

fof(f99,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f98,f43])).

fof(f98,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f97,f39])).

fof(f97,plain,
    ( ~ r1_partfun1(sK1,sK3)
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( ~ r1_partfun1(sK1,sK3)
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(resolution,[],[f94,f51])).

fof(f51,plain,
    ( v1_funct_2(sK3,sK0,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,sK0,X1)
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | k1_xboole_0 = X1 )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f93])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_partfun1(X0,sK0)
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f88,f101])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f87])).

fof(f118,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f103,f93,f54,f50,f42,f38,f26,f116])).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f55,f101])).

fof(f114,plain,
    ( spl4_17
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f102,f93,f54,f50,f42,f38,f26,f112])).

fof(f102,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f51,f101])).

fof(f95,plain,
    ( spl4_16
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f91,f87,f70,f93])).

fof(f70,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | k1_xboole_0 = X1 )
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0) )
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(resolution,[],[f88,f71])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( v1_partfun1(X2,X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X2) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f70])).

fof(f89,plain,
    ( spl4_15
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f85,f81,f62,f58,f87])).

fof(f58,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f62,plain,
    ( spl4_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f81,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_partfun1(sK1,X2)
        | ~ r1_partfun1(sK2,X2)
        | ~ v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_partfun1(X0,sK0) )
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f84,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f62])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_partfun1(X0,sK0) )
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(resolution,[],[f82,f59])).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_partfun1(sK1,X2)
        | ~ r1_partfun1(sK2,X2)
        | ~ v1_partfun1(X2,X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f79,f74,f46,f34,f30,f81])).

fof(f30,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f34,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f46,plain,
    ( spl4_6
  <=> r1_partfun1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f74,plain,
    ( spl4_13
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_partfun1(X2,X4)
        | ~ r1_partfun1(X3,X4)
        | ~ v1_partfun1(X4,X0)
        | r1_partfun1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_partfun1(sK1,X2)
        | ~ r1_partfun1(sK2,X2)
        | ~ v1_partfun1(X2,X0) )
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f78,f35])).

fof(f35,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_partfun1(sK1,X2)
        | ~ r1_partfun1(sK2,X2)
        | ~ v1_partfun1(X2,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl4_2
    | spl4_6
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f31,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_partfun1(sK1,X2)
        | ~ r1_partfun1(sK2,X2)
        | ~ v1_partfun1(X2,X0)
        | ~ v1_funct_1(sK1) )
    | spl4_6
    | ~ spl4_13 ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f75,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r1_partfun1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_partfun1(X2,X4)
        | ~ r1_partfun1(X3,X4)
        | ~ v1_partfun1(X4,X0)
        | ~ v1_funct_1(X2) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f23,f74])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X4)
      | ~ r1_partfun1(X3,X4)
      | ~ v1_partfun1(X4,X0)
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X4) )
             => ( ( v1_partfun1(X4,X0)
                  & r1_partfun1(X3,X4)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).

fof(f72,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f21,f70])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f68,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f24,f66])).

fof(f24,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f20,f62])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                  & v1_funct_2(X3,X0,X0)
                  & v1_funct_1(X3) )
               => ( ( r1_partfun1(X2,X3)
                    & r1_partfun1(X1,X3) )
                 => r1_partfun1(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
             => ( ( r1_partfun1(X2,X3)
                  & r1_partfun1(X1,X3) )
               => r1_partfun1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).

fof(f60,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f18,f58])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f13,f54])).

fof(f13,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f12,f50])).

fof(f12,plain,(
    v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f48,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f16,f46])).

fof(f16,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f15,f42])).

fof(f15,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f14,f38])).

fof(f14,plain,(
    r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:02:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.48  % (18768)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (18776)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (18780)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (18769)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (18772)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (18777)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (18772)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f48,f52,f56,f60,f64,f68,f72,f76,f83,f89,f95,f114,f118,f135,f146,f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ~spl4_1 | ~spl4_11 | ~spl4_17 | ~spl4_18 | spl4_23),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f147])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    $false | (~spl4_1 | ~spl4_11 | ~spl4_17 | ~spl4_18 | spl4_23)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f27,f113,f117,f145,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) ) | ~spl4_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    spl4_11 <=> ! [X1,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~v1_partfun1(sK3,k1_xboole_0) | spl4_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f144])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    spl4_23 <=> v1_partfun1(sK3,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl4_18 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl4_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    spl4_17 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    v1_funct_1(sK3) | ~spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    spl4_1 <=> v1_funct_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~spl4_23 | ~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_18 | ~spl4_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f141,f133,f116,f42,f38,f26,f144])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    spl4_4 <=> r1_partfun1(sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl4_5 <=> r1_partfun1(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    spl4_22 <=> ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ~v1_partfun1(sK3,k1_xboole_0) | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_18 | ~spl4_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f27])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ~v1_partfun1(sK3,k1_xboole_0) | ~v1_funct_1(sK3) | (~spl4_4 | ~spl4_5 | ~spl4_18 | ~spl4_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f139,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    r1_partfun1(sK1,sK3) | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f38])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ~r1_partfun1(sK1,sK3) | ~v1_partfun1(sK3,k1_xboole_0) | ~v1_funct_1(sK3) | (~spl4_5 | ~spl4_18 | ~spl4_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f136,f117])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~r1_partfun1(sK1,sK3) | ~v1_partfun1(sK3,k1_xboole_0) | ~v1_funct_1(sK3) | (~spl4_5 | ~spl4_22)),
% 0.22/0.51    inference(resolution,[],[f134,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    r1_partfun1(sK2,sK3) | ~spl4_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f42])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_partfun1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~r1_partfun1(sK1,X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0)) ) | ~spl4_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f133])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl4_22 | ~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_15 | ~spl4_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f108,f93,f87,f54,f50,f42,f38,f26,f133])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl4_7 <=> v1_funct_2(sK3,sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    spl4_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl4_15 <=> ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_partfun1(X0,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl4_16 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | k1_xboole_0 = X1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0)) ) | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_15 | ~spl4_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f106,f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f100,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f54])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f99,f27])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | (~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f98,f43])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | (~spl4_4 | ~spl4_7 | ~spl4_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f39])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ~r1_partfun1(sK1,sK3) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | (~spl4_7 | ~spl4_16)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f96])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ~r1_partfun1(sK1,sK3) | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | (~spl4_7 | ~spl4_16)),
% 0.22/0.51    inference(resolution,[],[f94,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK0,sK0) | ~spl4_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f50])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_funct_2(X0,sK0,X1) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | k1_xboole_0 = X1) ) | ~spl4_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f93])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_partfun1(X0,sK0) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0)) ) | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_15 | ~spl4_16)),
% 0.22/0.51    inference(backward_demodulation,[],[f88,f101])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_partfun1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0)) ) | ~spl4_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    spl4_18 | ~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f103,f93,f54,f50,f42,f38,f26,f116])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_16)),
% 0.22/0.51    inference(backward_demodulation,[],[f55,f101])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl4_17 | ~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f102,f93,f54,f50,f42,f38,f26,f112])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_16)),
% 0.22/0.51    inference(backward_demodulation,[],[f51,f101])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl4_16 | ~spl4_12 | ~spl4_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f91,f87,f70,f93])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    spl4_12 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | k1_xboole_0 = X1) ) | (~spl4_12 | ~spl4_15)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | k1_xboole_0 = X1 | ~v1_funct_1(X0)) ) | (~spl4_12 | ~spl4_15)),
% 0.22/0.51    inference(resolution,[],[f88,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_1(X2)) ) | ~spl4_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f70])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl4_15 | ~spl4_9 | ~spl4_10 | ~spl4_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f85,f81,f62,f58,f87])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl4_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl4_10 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl4_14 <=> ! [X1,X0,X2] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(sK1,X2) | ~r1_partfun1(sK2,X2) | ~v1_partfun1(X2,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_partfun1(X0,sK0)) ) | (~spl4_9 | ~spl4_10 | ~spl4_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f84,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f62])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X0) | ~r1_partfun1(sK2,X0) | ~v1_partfun1(X0,sK0)) ) | (~spl4_9 | ~spl4_14)),
% 0.22/0.51    inference(resolution,[],[f82,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f58])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(sK1,X2) | ~r1_partfun1(sK2,X2) | ~v1_partfun1(X2,X0)) ) | ~spl4_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl4_14 | ~spl4_2 | ~spl4_3 | spl4_6 | ~spl4_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f79,f74,f46,f34,f30,f81])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    spl4_2 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    spl4_3 <=> v1_funct_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    spl4_6 <=> r1_partfun1(sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    spl4_13 <=> ! [X1,X3,X0,X2,X4] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X4) | ~r1_partfun1(X3,X4) | ~v1_partfun1(X4,X0) | r1_partfun1(X2,X3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(sK1,X2) | ~r1_partfun1(sK2,X2) | ~v1_partfun1(X2,X0)) ) | (~spl4_2 | ~spl4_3 | spl4_6 | ~spl4_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f78,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    v1_funct_1(sK1) | ~spl4_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f34])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(sK1,X2) | ~r1_partfun1(sK2,X2) | ~v1_partfun1(X2,X0) | ~v1_funct_1(sK1)) ) | (~spl4_2 | spl4_6 | ~spl4_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f77,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v1_funct_1(sK2) | ~spl4_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f30])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(sK1,X2) | ~r1_partfun1(sK2,X2) | ~v1_partfun1(X2,X0) | ~v1_funct_1(sK1)) ) | (spl4_6 | ~spl4_13)),
% 0.22/0.51    inference(resolution,[],[f75,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~r1_partfun1(sK1,sK2) | spl4_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f46])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X4) | ~r1_partfun1(X3,X4) | ~v1_partfun1(X4,X0) | ~v1_funct_1(X2)) ) | ~spl4_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f74])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    spl4_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f74])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X4) | ~r1_partfun1(X3,X4) | ~v1_partfun1(X4,X0) | r1_partfun1(X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (r1_partfun1(X2,X3) | ~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((r1_partfun1(X2,X3) | (~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ((v1_partfun1(X4,X0) & r1_partfun1(X3,X4) & r1_partfun1(X2,X4)) => r1_partfun1(X2,X3)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl4_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f21,f70])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl4_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f66])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | v1_partfun1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl4_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f62])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f5])).
% 0.22/0.51  fof(f5,plain,(
% 0.22/0.51    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_partfun1(X1,X2) & (r1_partfun1(X2,X3) & r1_partfun1(X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & r1_partfun1(X1,X3)) => r1_partfun1(X1,X2)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f3])).
% 0.22/0.51  fof(f3,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & r1_partfun1(X1,X3)) => r1_partfun1(X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f58])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    spl4_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f13,f54])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl4_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f12,f50])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~spl4_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f16,f46])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ~r1_partfun1(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f15,f42])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    r1_partfun1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f14,f38])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    r1_partfun1(sK1,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f34])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    spl4_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f11,f26])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (18772)------------------------------
% 0.22/0.51  % (18772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18772)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (18772)Memory used [KB]: 10618
% 0.22/0.51  % (18772)Time elapsed: 0.063 s
% 0.22/0.51  % (18772)------------------------------
% 0.22/0.51  % (18772)------------------------------
% 0.22/0.51  % (18762)Success in time 0.147 s
%------------------------------------------------------------------------------
