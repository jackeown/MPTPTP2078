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
% DateTime   : Thu Dec  3 13:15:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 232 expanded)
%              Number of leaves         :   36 ( 104 expanded)
%              Depth                    :    7
%              Number of atoms          :  475 ( 788 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f78,f82,f86,f90,f98,f102,f114,f120,f124,f134,f143,f149,f157,f165,f174,f204,f237,f255,f267,f283,f448,f461])).

fof(f461,plain,
    ( spl3_5
    | ~ spl3_20
    | ~ spl3_65 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | spl3_5
    | ~ spl3_20
    | ~ spl3_65 ),
    inference(subsumption_resolution,[],[f457,f133])).

fof(f133,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f457,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_5
    | ~ spl3_65 ),
    inference(resolution,[],[f447,f69])).

fof(f69,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_5
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f447,plain,
    ( ! [X0] :
        ( m2_connsp_2(k2_struct_0(sK0),sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl3_65
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f448,plain,
    ( spl3_65
    | ~ spl3_27
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f288,f281,f172,f446])).

fof(f172,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f281,plain,
    ( spl3_44
  <=> ! [X0] :
        ( r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) )
    | ~ spl3_27
    | ~ spl3_44 ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) )
    | ~ spl3_27
    | ~ spl3_44 ),
    inference(resolution,[],[f282,f173])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f172])).

fof(f282,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( spl3_44
    | ~ spl3_8
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f272,f253,f80,f281])).

fof(f80,plain,
    ( spl3_8
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f253,plain,
    ( spl3_40
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f272,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_8
    | ~ spl3_40 ),
    inference(resolution,[],[f254,f81])).

fof(f81,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X1))
        | r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f253])).

fof(f267,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | spl3_39 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7
    | spl3_39 ),
    inference(subsumption_resolution,[],[f264,f61])).

fof(f61,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f264,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_7
    | spl3_39 ),
    inference(resolution,[],[f251,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f251,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_39 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl3_39
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f255,plain,
    ( ~ spl3_39
    | spl3_40
    | spl3_1
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f238,f235,f52,f253,f250])).

fof(f52,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f235,plain,
    ( spl3_37
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
        | ~ l1_struct_0(X2)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X1))
        | ~ l1_struct_0(sK0)
        | r1_tarski(X0,X1) )
    | spl3_1
    | ~ spl3_37 ),
    inference(resolution,[],[f236,f53])).

fof(f53,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f236,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
        | ~ l1_struct_0(X2)
        | r1_tarski(X0,X1) )
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f235])).

fof(f237,plain,
    ( spl3_37
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f209,f202,f88,f235])).

fof(f88,plain,
    ( spl3_10
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f202,plain,
    ( spl3_31
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
        | ~ l1_struct_0(X2)
        | v2_struct_0(X2) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(resolution,[],[f203,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X2)
        | r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( spl3_31
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f175,f155,f96,f202])).

fof(f96,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f155,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(resolution,[],[f156,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f155])).

fof(f174,plain,
    ( spl3_27
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f170,f163,f118,f80,f60,f56,f172])).

fof(f56,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f118,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f163,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f169,f57])).

fof(f57,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f168,f61])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f167,f81])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(superposition,[],[f164,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( spl3_26
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f161,f147,f141,f60,f56,f163])).

fof(f141,plain,
    ( spl3_22
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f147,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(X1,k1_tops_1(X0,X2))
        | m2_connsp_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f160,f142])).

fof(f142,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f141])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f159,f142])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f158,f61])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(resolution,[],[f148,f57])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(X1,k1_tops_1(X0,X2))
        | m2_connsp_2(X2,X0,X1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f157,plain,
    ( spl3_25
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f116,f112,f100,f155])).

fof(f100,plain,
    ( spl3_13
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f112,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(resolution,[],[f113,f101])).

fof(f101,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f112])).

fof(f149,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f37,f147])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f143,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f129,f122,f60,f141])).

fof(f122,plain,
    ( spl3_18
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f129,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(resolution,[],[f123,f61])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f134,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f130,f122,f64,f60,f132])).

fof(f64,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f130,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f65,f129])).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f124,plain,
    ( spl3_18
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f115,f84,f76,f122])).

fof(f84,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f115,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(resolution,[],[f85,f77])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f120,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f36,f118])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f114,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f42,f112])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f102,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f48,f100])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f98,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f86,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f33,f84])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f82,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f50,f80])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f78,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f70,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:45:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (19046)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (19042)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (19045)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (19036)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (19042)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (19046)Refutation not found, incomplete strategy% (19046)------------------------------
% 0.21/0.47  % (19046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19046)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19046)Memory used [KB]: 1663
% 0.21/0.47  % (19046)Time elapsed: 0.070 s
% 0.21/0.47  % (19046)------------------------------
% 0.21/0.47  % (19046)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f468,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f78,f82,f86,f90,f98,f102,f114,f120,f124,f134,f143,f149,f157,f165,f174,f204,f237,f255,f267,f283,f448,f461])).
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    spl3_5 | ~spl3_20 | ~spl3_65),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f460])).
% 0.21/0.48  fof(f460,plain,(
% 0.21/0.48    $false | (spl3_5 | ~spl3_20 | ~spl3_65)),
% 0.21/0.48    inference(subsumption_resolution,[],[f457,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl3_20 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f457,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (spl3_5 | ~spl3_65)),
% 0.21/0.48    inference(resolution,[],[f447,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl3_5 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f447,plain,(
% 0.21/0.48    ( ! [X0] : (m2_connsp_2(k2_struct_0(sK0),sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_65),
% 0.21/0.48    inference(avatar_component_clause,[],[f446])).
% 0.21/0.48  fof(f446,plain,(
% 0.21/0.48    spl3_65 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.21/0.48  fof(f448,plain,(
% 0.21/0.48    spl3_65 | ~spl3_27 | ~spl3_44),
% 0.21/0.48    inference(avatar_split_clause,[],[f288,f281,f172,f446])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl3_27 <=> ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    spl3_44 <=> ! [X0] : (r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) ) | (~spl3_27 | ~spl3_44)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f285])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) ) | (~spl3_27 | ~spl3_44)),
% 0.21/0.48    inference(resolution,[],[f282,f173])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) ) | ~spl3_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f172])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_44),
% 0.21/0.48    inference(avatar_component_clause,[],[f281])).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    spl3_44 | ~spl3_8 | ~spl3_40),
% 0.21/0.48    inference(avatar_split_clause,[],[f272,f253,f80,f281])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl3_8 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    spl3_40 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl3_8 | ~spl3_40)),
% 0.21/0.48    inference(resolution,[],[f254,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X1)) | r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_40),
% 0.21/0.48    inference(avatar_component_clause,[],[f253])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_7 | spl3_39),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f266])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    $false | (~spl3_3 | ~spl3_7 | spl3_39)),
% 0.21/0.48    inference(subsumption_resolution,[],[f264,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl3_3 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl3_7 | spl3_39)),
% 0.21/0.48    inference(resolution,[],[f251,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl3_7 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ~l1_struct_0(sK0) | spl3_39),
% 0.21/0.48    inference(avatar_component_clause,[],[f250])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    spl3_39 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ~spl3_39 | spl3_40 | spl3_1 | ~spl3_37),
% 0.21/0.48    inference(avatar_split_clause,[],[f238,f235,f52,f253,f250])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    spl3_37 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) | ~l1_struct_0(X2) | v2_struct_0(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X1)) | ~l1_struct_0(sK0) | r1_tarski(X0,X1)) ) | (spl3_1 | ~spl3_37)),
% 0.21/0.48    inference(resolution,[],[f236,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) | ~l1_struct_0(X2) | r1_tarski(X0,X1)) ) | ~spl3_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f235])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    spl3_37 | ~spl3_10 | ~spl3_31),
% 0.21/0.48    inference(avatar_split_clause,[],[f209,f202,f88,f235])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_10 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    spl3_31 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) | ~l1_struct_0(X2) | v2_struct_0(X2)) ) | (~spl3_10 | ~spl3_31)),
% 0.21/0.48    inference(resolution,[],[f203,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) ) | ~spl3_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f202])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    spl3_31 | ~spl3_12 | ~spl3_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f175,f155,f96,f202])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl3_12 <=> ! [X1,X0] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    spl3_25 <=> ! [X1,X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) ) | (~spl3_12 | ~spl3_25)),
% 0.21/0.48    inference(resolution,[],[f156,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | ~spl3_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f155])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    spl3_27 | ~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_17 | ~spl3_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f170,f163,f118,f80,f60,f56,f172])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl3_2 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    spl3_17 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    spl3_26 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_17 | ~spl3_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0) | ~v2_pre_topc(sK0)) ) | (~spl3_3 | ~spl3_8 | ~spl3_17 | ~spl3_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f168,f61])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_17 | ~spl3_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f167,f81])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl3_17 | ~spl3_26)),
% 0.21/0.48    inference(superposition,[],[f164,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f118])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0)) ) | ~spl3_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f163])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    spl3_26 | ~spl3_2 | ~spl3_3 | ~spl3_22 | ~spl3_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f161,f147,f141,f60,f56,f163])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl3_22 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl3_23 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_22 | ~spl3_23)),
% 0.21/0.48    inference(forward_demodulation,[],[f160,f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f141])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_22 | ~spl3_23)),
% 0.21/0.48    inference(forward_demodulation,[],[f159,f142])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f158,f61])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_23)),
% 0.21/0.48    inference(resolution,[],[f148,f57])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) ) | ~spl3_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f147])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl3_25 | ~spl3_13 | ~spl3_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f116,f112,f100,f155])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl3_13 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl3_16 <=> ! [X1,X0] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl3_13 | ~spl3_16)),
% 0.21/0.48    inference(resolution,[],[f113,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) ) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f112])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl3_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f147])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl3_22 | ~spl3_3 | ~spl3_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f129,f122,f60,f141])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl3_18 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_3 | ~spl3_18)),
% 0.21/0.48    inference(resolution,[],[f123,f61])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f122])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl3_20 | ~spl3_3 | ~spl3_4 | ~spl3_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f130,f122,f64,f60,f132])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_4 | ~spl3_18)),
% 0.21/0.48    inference(backward_demodulation,[],[f65,f129])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl3_18 | ~spl3_7 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f115,f84,f76,f122])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl3_9 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl3_7 | ~spl3_9)),
% 0.21/0.48    inference(resolution,[],[f85,f77])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl3_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f118])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl3_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f112])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f100])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f96])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f88])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f84])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f50,f80])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f32,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f76])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f68])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f64])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f60])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f56])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f52])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (19042)------------------------------
% 0.21/0.48  % (19042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19042)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (19042)Memory used [KB]: 10874
% 0.21/0.48  % (19042)Time elapsed: 0.067 s
% 0.21/0.48  % (19042)------------------------------
% 0.21/0.48  % (19042)------------------------------
% 0.21/0.48  % (19027)Success in time 0.117 s
%------------------------------------------------------------------------------
