%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 277 expanded)
%              Number of leaves         :   42 ( 132 expanded)
%              Depth                    :    6
%              Number of atoms          :  437 ( 739 expanded)
%              Number of equality atoms :   58 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f60,f64,f68,f72,f76,f84,f89,f95,f99,f103,f107,f113,f129,f139,f145,f149,f160,f168,f179,f186,f201,f207,f223,f232,f254,f275,f282,f287,f337,f355])).

fof(f355,plain,
    ( spl3_27
    | ~ spl3_3
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f351,f199,f50,f171])).

fof(f171,plain,
    ( spl3_27
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f50,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f199,plain,
    ( spl3_32
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f351,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f51,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f199])).

fof(f51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f337,plain,
    ( spl3_32
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f303,f177,f66,f199])).

fof(f66,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f177,plain,
    ( spl3_28
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f303,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(resolution,[],[f178,f67])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f178,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f177])).

fof(f287,plain,
    ( ~ spl3_9
    | ~ spl3_36
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_36
    | spl3_38 ),
    inference(subsumption_resolution,[],[f284,f231])).

fof(f231,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl3_36
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f284,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_9
    | spl3_38 ),
    inference(resolution,[],[f281,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f281,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_38 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl3_38
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f282,plain,
    ( ~ spl3_38
    | ~ spl3_13
    | ~ spl3_27
    | spl3_37 ),
    inference(avatar_split_clause,[],[f278,f273,f171,f93,f280])).

fof(f93,plain,
    ( spl3_13
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f273,plain,
    ( spl3_37
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f278,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl3_13
    | ~ spl3_27
    | spl3_37 ),
    inference(subsumption_resolution,[],[f277,f172])).

fof(f172,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f171])).

fof(f277,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_13
    | spl3_37 ),
    inference(superposition,[],[f274,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( k8_setfam_1(X0,k1_xboole_0) = X0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f274,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f273])).

fof(f275,plain,
    ( ~ spl3_37
    | spl3_29
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f263,f199,f184,f273])).

fof(f184,plain,
    ( spl3_29
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f263,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_29
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f185,f200])).

fof(f185,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f184])).

fof(f254,plain,
    ( spl3_12
    | ~ spl3_23
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl3_12
    | ~ spl3_23
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f252,f148])).

fof(f148,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_23
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f252,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl3_12
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f237,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_25
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f237,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl3_12
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f88,f200])).

fof(f88,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_12
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f232,plain,
    ( spl3_36
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f189,f155,f111,f46,f230])).

fof(f46,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f111,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f155,plain,
    ( spl3_24
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f189,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f188,f47])).

fof(f47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f188,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(superposition,[],[f112,f156])).

fof(f156,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f155])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f223,plain,
    ( spl3_32
    | ~ spl3_1
    | ~ spl3_14
    | spl3_33 ),
    inference(avatar_split_clause,[],[f210,f205,f97,f42,f199])).

fof(f42,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f97,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = X0
        | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f205,plain,
    ( spl3_33
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f210,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | ~ spl3_14
    | spl3_33 ),
    inference(subsumption_resolution,[],[f208,f43])).

fof(f43,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f208,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_14
    | spl3_33 ),
    inference(resolution,[],[f206,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f206,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( ~ spl3_33
    | spl3_29
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f203,f196,f184,f205])).

fof(f196,plain,
    ( spl3_31
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f203,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_29
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f185,f197])).

fof(f197,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f196])).

fof(f201,plain,
    ( spl3_31
    | spl3_32
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f151,f143,f50,f199,f196])).

fof(f143,plain,
    ( spl3_22
  <=> ! [X3,X2] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(resolution,[],[f144,f51])).

fof(f144,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | k1_xboole_0 = X3
        | k1_setfam_1(X3) = k8_setfam_1(X2,X3) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f143])).

fof(f186,plain,
    ( ~ spl3_29
    | spl3_4
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f181,f155,f54,f184])).

fof(f54,plain,
    ( spl3_4
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f181,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_4
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f55,f156])).

fof(f55,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f179,plain,
    ( spl3_28
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f169,f166,f101,f177])).

fof(f101,plain,
    ( spl3_15
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f166,plain,
    ( spl3_26
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f169,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(resolution,[],[f167,f102])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f167,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl3_26
    | ~ spl3_1
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f164,f158,f42,f166])).

fof(f164,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f43,f159])).

fof(f160,plain,
    ( spl3_24
    | spl3_25
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f150,f143,f46,f158,f155])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(resolution,[],[f144,f47])).

fof(f149,plain,
    ( spl3_23
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f141,f137,f70,f62,f147])).

fof(f62,plain,
    ( spl3_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f70,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f137,plain,
    ( spl3_21
  <=> ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f141,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f140,f63])).

fof(f63,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f140,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(resolution,[],[f138,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(X0,k1_zfmisc_1(X0)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f137])).

fof(f145,plain,
    ( spl3_22
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f135,f127,f105,f143])).

fof(f105,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f127,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = X1
        | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f135,plain,
    ( ! [X2,X3] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) )
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ! [X2,X3] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) )
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(superposition,[],[f128,f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f139,plain,
    ( spl3_21
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f121,f111,f93,f137])).

fof(f121,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(superposition,[],[f112,f94])).

fof(f129,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f37,f127])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f113,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f35,f111])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f107,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f34,f105])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f103,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f90,f82,f58,f101])).

fof(f58,plain,
    ( spl3_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( v1_xboole_0(X1)
        | ~ r1_tarski(X1,X0)
        | ~ r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f83,f59])).

fof(f59,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f99,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f33,f97])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f95,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f40,f93])).

fof(f40,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,
    ( ~ spl3_12
    | spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f85,f74,f54,f87])).

fof(f85,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f75,f55])).

fof(f84,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f76,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f38,f70])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f64,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f60,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f56,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (32666)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (32662)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (32663)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (32670)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (32667)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (32664)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (32668)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (32670)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (32674)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (32662)Refutation not found, incomplete strategy% (32662)------------------------------
% 0.20/0.50  % (32662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32662)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32662)Memory used [KB]: 10490
% 0.20/0.50  % (32662)Time elapsed: 0.075 s
% 0.20/0.50  % (32662)------------------------------
% 0.20/0.50  % (32662)------------------------------
% 0.20/0.50  % (32674)Refutation not found, incomplete strategy% (32674)------------------------------
% 0.20/0.50  % (32674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f356,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f60,f64,f68,f72,f76,f84,f89,f95,f99,f103,f107,f113,f129,f139,f145,f149,f160,f168,f179,f186,f201,f207,f223,f232,f254,f275,f282,f287,f337,f355])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    spl3_27 | ~spl3_3 | ~spl3_32),
% 0.20/0.50    inference(avatar_split_clause,[],[f351,f199,f50,f171])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    spl3_27 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    spl3_32 <=> k1_xboole_0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.50  fof(f351,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_3 | ~spl3_32)),
% 0.20/0.50    inference(forward_demodulation,[],[f51,f200])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl3_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f199])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f50])).
% 0.20/0.50  fof(f337,plain,(
% 0.20/0.50    spl3_32 | ~spl3_7 | ~spl3_28),
% 0.20/0.50    inference(avatar_split_clause,[],[f303,f177,f66,f199])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    spl3_7 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    spl3_28 <=> v1_xboole_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | (~spl3_7 | ~spl3_28)),
% 0.20/0.50    inference(resolution,[],[f178,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f66])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    v1_xboole_0(sK1) | ~spl3_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f177])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    ~spl3_9 | ~spl3_36 | spl3_38),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f286])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    $false | (~spl3_9 | ~spl3_36 | spl3_38)),
% 0.20/0.50    inference(subsumption_resolution,[],[f284,f231])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_36),
% 0.20/0.50    inference(avatar_component_clause,[],[f230])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    spl3_36 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_9 | spl3_38)),
% 0.20/0.50    inference(resolution,[],[f281,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f280])).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    spl3_38 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    ~spl3_38 | ~spl3_13 | ~spl3_27 | spl3_37),
% 0.20/0.50    inference(avatar_split_clause,[],[f278,f273,f171,f93,f280])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl3_13 <=> ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    spl3_37 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),sK0) | (~spl3_13 | ~spl3_27 | spl3_37)),
% 0.20/0.50    inference(subsumption_resolution,[],[f277,f172])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f171])).
% 0.20/0.50  fof(f277,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_13 | spl3_37)),
% 0.20/0.50    inference(superposition,[],[f274,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f93])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_37),
% 0.20/0.50    inference(avatar_component_clause,[],[f273])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    ~spl3_37 | spl3_29 | ~spl3_32),
% 0.20/0.50    inference(avatar_split_clause,[],[f263,f199,f184,f273])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    spl3_29 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_29 | ~spl3_32)),
% 0.20/0.50    inference(forward_demodulation,[],[f185,f200])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | spl3_29),
% 0.20/0.50    inference(avatar_component_clause,[],[f184])).
% 0.20/0.50  fof(f254,plain,(
% 0.20/0.50    spl3_12 | ~spl3_23 | ~spl3_25 | ~spl3_32),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f253])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    $false | (spl3_12 | ~spl3_23 | ~spl3_25 | ~spl3_32)),
% 0.20/0.50    inference(subsumption_resolution,[],[f252,f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f147])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    spl3_23 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    ~m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (spl3_12 | ~spl3_25 | ~spl3_32)),
% 0.20/0.50    inference(forward_demodulation,[],[f237,f159])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | ~spl3_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f158])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    spl3_25 <=> k1_xboole_0 = sK2),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (spl3_12 | ~spl3_32)),
% 0.20/0.50    inference(forward_demodulation,[],[f88,f200])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl3_12 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    spl3_36 | ~spl3_2 | ~spl3_17 | ~spl3_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f189,f155,f111,f46,f230])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl3_17 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl3_24 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_17 | ~spl3_24)),
% 0.20/0.50    inference(subsumption_resolution,[],[f188,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f46])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_17 | ~spl3_24)),
% 0.20/0.50    inference(superposition,[],[f112,f156])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f155])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f111])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    spl3_32 | ~spl3_1 | ~spl3_14 | spl3_33),
% 0.20/0.50    inference(avatar_split_clause,[],[f210,f205,f97,f42,f199])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl3_14 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl3_33 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | (~spl3_1 | ~spl3_14 | spl3_33)),
% 0.20/0.50    inference(subsumption_resolution,[],[f208,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f42])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl3_14 | spl3_33)),
% 0.20/0.50    inference(resolution,[],[f206,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f97])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_33),
% 0.20/0.50    inference(avatar_component_clause,[],[f205])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    ~spl3_33 | spl3_29 | ~spl3_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f203,f196,f184,f205])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    spl3_31 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl3_29 | ~spl3_31)),
% 0.20/0.50    inference(backward_demodulation,[],[f185,f197])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f196])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    spl3_31 | spl3_32 | ~spl3_3 | ~spl3_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f151,f143,f50,f199,f196])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl3_22 <=> ! [X3,X2] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | (~spl3_3 | ~spl3_22)),
% 0.20/0.50    inference(resolution,[],[f144,f51])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) ) | ~spl3_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f143])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    ~spl3_29 | spl3_4 | ~spl3_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f181,f155,f54,f184])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    spl3_4 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl3_4 | ~spl3_24)),
% 0.20/0.50    inference(backward_demodulation,[],[f55,f156])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f54])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    spl3_28 | ~spl3_15 | ~spl3_26),
% 0.20/0.50    inference(avatar_split_clause,[],[f169,f166,f101,f177])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl3_15 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    spl3_26 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    v1_xboole_0(sK1) | (~spl3_15 | ~spl3_26)),
% 0.20/0.50    inference(resolution,[],[f167,f102])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | ~spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f101])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    r1_tarski(sK1,k1_xboole_0) | ~spl3_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f166])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    spl3_26 | ~spl3_1 | ~spl3_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f164,f158,f42,f166])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    r1_tarski(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_25)),
% 0.20/0.50    inference(backward_demodulation,[],[f43,f159])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    spl3_24 | spl3_25 | ~spl3_2 | ~spl3_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f150,f143,f46,f158,f155])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | (~spl3_2 | ~spl3_22)),
% 0.20/0.50    inference(resolution,[],[f144,f47])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    spl3_23 | ~spl3_6 | ~spl3_8 | ~spl3_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f141,f137,f70,f62,f147])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl3_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl3_8 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl3_21 <=> ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl3_6 | ~spl3_8 | ~spl3_21)),
% 0.20/0.50    inference(subsumption_resolution,[],[f140,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f62])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~r1_tarski(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl3_8 | ~spl3_21)),
% 0.20/0.50    inference(resolution,[],[f138,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f70])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f137])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    spl3_22 | ~spl3_16 | ~spl3_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f135,f127,f105,f143])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl3_16 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    spl3_20 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) ) | (~spl3_16 | ~spl3_20)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) ) | (~spl3_16 | ~spl3_20)),
% 0.20/0.50    inference(superposition,[],[f128,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f105])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f127])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl3_21 | ~spl3_13 | ~spl3_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f121,f111,f93,f137])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_13 | ~spl3_17)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_13 | ~spl3_17)),
% 0.20/0.50    inference(superposition,[],[f112,f94])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    spl3_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f127])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl3_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f35,f111])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    spl3_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f34,f105])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl3_15 | ~spl3_5 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f90,f82,f58,f101])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl3_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl3_11 <=> ! [X1,X0] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | (~spl3_5 | ~spl3_11)),
% 0.20/0.50    inference(resolution,[],[f83,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) ) | ~spl3_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f82])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl3_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f33,f97])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    spl3_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f40,f93])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(equality_resolution,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ~spl3_12 | spl3_4 | ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f85,f74,f54,f87])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | (spl3_4 | ~spl3_9)),
% 0.20/0.50    inference(resolution,[],[f75,f55])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f82])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f74])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f70])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f66])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f62])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f58])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ~spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f26,f54])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f50])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f24,f46])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f25,f42])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    r1_tarski(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (32670)------------------------------
% 0.20/0.50  % (32670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32670)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (32670)Memory used [KB]: 10746
% 0.20/0.50  % (32670)Time elapsed: 0.072 s
% 0.20/0.50  % (32670)------------------------------
% 0.20/0.50  % (32670)------------------------------
% 0.20/0.50  % (32660)Success in time 0.149 s
%------------------------------------------------------------------------------
