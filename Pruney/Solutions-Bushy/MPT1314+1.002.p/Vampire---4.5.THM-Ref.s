%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1314+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:43 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 253 expanded)
%              Number of leaves         :   37 ( 110 expanded)
%              Depth                    :    7
%              Number of atoms          :  460 ( 882 expanded)
%              Number of equality atoms :   34 (  84 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f56,f60,f64,f68,f72,f76,f80,f84,f92,f96,f100,f105,f109,f113,f120,f126,f159,f176,f191,f204,f208,f213,f226,f230,f266,f280,f316])).

fof(f316,plain,
    ( ~ spl5_4
    | spl5_5
    | ~ spl5_18
    | ~ spl5_36
    | ~ spl5_45 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl5_4
    | spl5_5
    | ~ spl5_18
    | ~ spl5_36
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f314,f229])).

fof(f229,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl5_36
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f314,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_4
    | spl5_5
    | ~ spl5_18
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f313,f119])).

fof(f119,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f313,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_4
    | spl5_5
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f309,f59])).

fof(f59,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f309,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | spl5_5
    | ~ spl5_45 ),
    inference(resolution,[],[f279,f63])).

fof(f63,plain,
    ( ~ v3_pre_topc(sK1,sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_5
  <=> v3_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f279,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) )
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl5_45
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f280,plain,
    ( spl5_45
    | ~ spl5_12
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f267,f264,f90,f278])).

fof(f90,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f264,plain,
    ( spl5_43
  <=> ! [X0] :
        ( v3_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,k2_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) )
    | ~ spl5_12
    | ~ spl5_43 ),
    inference(resolution,[],[f265,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK2) )
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( spl5_43
    | ~ spl5_14
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f250,f189,f98,f264])).

fof(f98,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f189,plain,
    ( spl5_31
  <=> ! [X0] :
        ( v3_pre_topc(k3_xboole_0(X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f250,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,k2_struct_0(sK2)) )
    | ~ spl5_14
    | ~ spl5_31 ),
    inference(superposition,[],[f190,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f190,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f189])).

fof(f230,plain,
    ( spl5_36
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f216,f211,f70,f54,f46,f228])).

fof(f46,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f54,plain,
    ( spl5_3
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f70,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f211,plain,
    ( spl5_35
  <=> ! [X1,X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f216,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_35 ),
    inference(backward_demodulation,[],[f71,f215])).

fof(f215,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f214,f47])).

fof(f47,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f214,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_35 ),
    inference(resolution,[],[f212,f55])).

fof(f55,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X1) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f211])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f226,plain,
    ( ~ spl5_32
    | ~ spl5_8
    | spl5_34 ),
    inference(avatar_split_clause,[],[f209,f206,f74,f196])).

fof(f196,plain,
    ( spl5_32
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f74,plain,
    ( spl5_8
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f206,plain,
    ( spl5_34
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl5_8
    | spl5_34 ),
    inference(resolution,[],[f207,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f207,plain,
    ( ~ l1_struct_0(sK2)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f206])).

fof(f213,plain,
    ( spl5_35
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f115,f103,f82,f211])).

fof(f82,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f103,plain,
    ( spl5_15
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(resolution,[],[f104,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f208,plain,
    ( ~ spl5_34
    | ~ spl5_13
    | spl5_30 ),
    inference(avatar_split_clause,[],[f193,f186,f94,f206])).

fof(f94,plain,
    ( spl5_13
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f186,plain,
    ( spl5_30
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f193,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl5_13
    | spl5_30 ),
    inference(resolution,[],[f187,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_struct_0(X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f187,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f186])).

fof(f204,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_10
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_10
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f47,f55,f197,f83])).

fof(f197,plain,
    ( ~ l1_pre_topc(sK2)
    | spl5_32 ),
    inference(avatar_component_clause,[],[f196])).

fof(f191,plain,
    ( ~ spl5_30
    | spl5_31
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f180,f174,f111,f107,f189,f186])).

fof(f107,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f111,plain,
    ( spl5_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f174,plain,
    ( spl5_28
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f180,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(X0,k2_struct_0(sK2)),sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f178,f122])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_16
    | ~ spl5_17 ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_16
    | ~ spl5_17 ),
    inference(superposition,[],[f108,f112])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f178,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k3_xboole_0(X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl5_17
    | ~ spl5_28 ),
    inference(superposition,[],[f175,f112])).

fof(f175,plain,
    ( ! [X0] :
        ( v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f174])).

fof(f176,plain,
    ( spl5_28
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_19
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f166,f157,f124,f54,f46,f174])).

fof(f124,plain,
    ( spl5_19
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f157,plain,
    ( spl5_25
  <=> ! [X1,X3,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X3,X0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_19
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f165,f125])).

fof(f125,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f124])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f164,f47])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(resolution,[],[f158,f55])).

fof(f158,plain,
    ( ! [X0,X3,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X3,X0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,(
    spl5_25 ),
    inference(avatar_split_clause,[],[f42,f157])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v3_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

fof(f126,plain,
    ( spl5_19
    | ~ spl5_1
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f114,f103,f46,f124])).

fof(f114,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_15 ),
    inference(resolution,[],[f104,f47])).

fof(f120,plain,
    ( spl5_18
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f116,f103,f66,f46,f118])).

fof(f66,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f116,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(backward_demodulation,[],[f67,f114])).

fof(f67,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f113,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f41,f111])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f109,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f40,f107])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f105,plain,
    ( spl5_15
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f101,f78,f74,f103])).

fof(f78,plain,
    ( spl5_9
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f101,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f79,f75])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f100,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f37,f98])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f96,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f30,f94])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f92,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f39,f90])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

% (16020)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f84,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f80,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f29,f78])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f76,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f72,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f44,f70])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f22,f23])).

fof(f23,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f43,f62])).

fof(f43,plain,(
    ~ v3_pre_topc(sK1,sK2) ),
    inference(backward_demodulation,[],[f24,f23])).

fof(f24,plain,(
    ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f46])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
