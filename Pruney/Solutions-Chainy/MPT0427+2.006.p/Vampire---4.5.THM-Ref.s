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
% DateTime   : Thu Dec  3 12:46:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 312 expanded)
%              Number of leaves         :   49 ( 151 expanded)
%              Depth                    :    6
%              Number of atoms          :  489 ( 824 expanded)
%              Number of equality atoms :   66 ( 121 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f65,f69,f77,f81,f89,f95,f99,f103,f108,f112,f119,f125,f129,f133,f137,f142,f150,f161,f165,f175,f179,f190,f198,f209,f216,f231,f237,f253,f262,f284,f305,f312,f317,f369,f387])).

fof(f387,plain,
    ( spl4_32
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f383,f229,f55,f201])).

fof(f201,plain,
    ( spl4_32
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f55,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f229,plain,
    ( spl4_37
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f383,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f56,f230])).

fof(f230,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f229])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f369,plain,
    ( spl4_37
    | ~ spl4_6
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f334,f207,f67,f229])).

fof(f67,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f207,plain,
    ( spl4_33
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f334,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6
    | ~ spl4_33 ),
    inference(resolution,[],[f208,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f208,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f207])).

fof(f317,plain,
    ( ~ spl4_14
    | ~ spl4_41
    | spl4_43 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_41
    | spl4_43 ),
    inference(subsumption_resolution,[],[f314,f261])).

fof(f261,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl4_41
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f314,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_14
    | spl4_43 ),
    inference(resolution,[],[f311,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f311,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl4_43 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl4_43
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f312,plain,
    ( ~ spl4_43
    | ~ spl4_18
    | ~ spl4_32
    | spl4_42 ),
    inference(avatar_split_clause,[],[f308,f303,f201,f123,f310])).

fof(f123,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f303,plain,
    ( spl4_42
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f308,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl4_18
    | ~ spl4_32
    | spl4_42 ),
    inference(subsumption_resolution,[],[f307,f202])).

fof(f202,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f201])).

fof(f307,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_18
    | spl4_42 ),
    inference(superposition,[],[f304,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( k8_setfam_1(X0,k1_xboole_0) = X0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f304,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,
    ( ~ spl4_42
    | spl4_34
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f293,f229,f214,f303])).

fof(f214,plain,
    ( spl4_34
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f293,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl4_34
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f215,f230])).

fof(f215,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f214])).

fof(f284,plain,
    ( spl4_17
    | ~ spl4_28
    | ~ spl4_30
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl4_17
    | ~ spl4_28
    | ~ spl4_30
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f282,f178])).

fof(f178,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl4_28
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f282,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl4_17
    | ~ spl4_30
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f267,f189])).

fof(f189,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f267,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl4_17
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f118,f230])).

fof(f118,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_17
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f262,plain,
    ( spl4_41
    | ~ spl4_2
    | ~ spl4_22
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f219,f185,f140,f51,f260])).

fof(f51,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f140,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f185,plain,
    ( spl4_29
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f219,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_2
    | ~ spl4_22
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f218,f52])).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f218,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_22
    | ~ spl4_29 ),
    inference(superposition,[],[f141,f186])).

fof(f186,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f185])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f140])).

fof(f253,plain,
    ( spl4_37
    | ~ spl4_1
    | ~ spl4_19
    | spl4_38 ),
    inference(avatar_split_clause,[],[f240,f235,f127,f47,f229])).

fof(f47,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f127,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = X0
        | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f235,plain,
    ( spl4_38
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f240,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1
    | ~ spl4_19
    | spl4_38 ),
    inference(subsumption_resolution,[],[f238,f48])).

fof(f48,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f238,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_19
    | spl4_38 ),
    inference(resolution,[],[f236,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f236,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f235])).

fof(f237,plain,
    ( ~ spl4_38
    | spl4_34
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f233,f226,f214,f235])).

fof(f226,plain,
    ( spl4_36
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f233,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl4_34
    | ~ spl4_36 ),
    inference(backward_demodulation,[],[f215,f227])).

fof(f227,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f226])).

fof(f231,plain,
    ( spl4_36
    | spl4_37
    | ~ spl4_3
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f181,f173,f55,f229,f226])).

fof(f173,plain,
    ( spl4_27
  <=> ! [X3,X2] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f181,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_3
    | ~ spl4_27 ),
    inference(resolution,[],[f174,f56])).

fof(f174,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | k1_xboole_0 = X3
        | k1_setfam_1(X3) = k8_setfam_1(X2,X3) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f173])).

fof(f216,plain,
    ( ~ spl4_34
    | spl4_4
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f211,f185,f59,f214])).

fof(f59,plain,
    ( spl4_4
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f211,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl4_4
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f60,f186])).

fof(f60,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f209,plain,
    ( spl4_33
    | ~ spl4_24
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f199,f196,f148,f207])).

fof(f148,plain,
    ( spl4_24
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f196,plain,
    ( spl4_31
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f199,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_24
    | ~ spl4_31 ),
    inference(resolution,[],[f197,f149])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f148])).

fof(f197,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f196])).

fof(f198,plain,
    ( spl4_31
    | ~ spl4_1
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f194,f188,f47,f196])).

fof(f194,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f48,f189])).

fof(f190,plain,
    ( spl4_29
    | spl4_30
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f180,f173,f51,f188,f185])).

fof(f180,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(resolution,[],[f174,f52])).

fof(f179,plain,
    ( spl4_28
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f171,f159,f97,f63,f177])).

fof(f63,plain,
    ( spl4_5
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f97,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f159,plain,
    ( spl4_25
  <=> ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f171,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f170,f64])).

fof(f64,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f170,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl4_13
    | ~ spl4_25 ),
    inference(resolution,[],[f160,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(X0,k1_zfmisc_1(X0)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f159])).

fof(f175,plain,
    ( spl4_27
    | ~ spl4_21
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f169,f163,f135,f173])).

fof(f135,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f163,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = X1
        | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f169,plain,
    ( ! [X2,X3] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) )
    | ~ spl4_21
    | ~ spl4_26 ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ! [X2,X3] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) )
    | ~ spl4_21
    | ~ spl4_26 ),
    inference(superposition,[],[f164,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f135])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f37,f163])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f161,plain,
    ( spl4_25
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f155,f140,f123,f159])).

fof(f155,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(superposition,[],[f141,f124])).

fof(f150,plain,
    ( spl4_24
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f138,f131,f97,f148])).

fof(f131,plain,
    ( spl4_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f138,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(resolution,[],[f132,f98])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f131])).

fof(f142,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f35,f140])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f137,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f34,f135])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f133,plain,
    ( spl4_20
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f120,f110,f106,f131])).

fof(f106,plain,
    ( spl4_15
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f110,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(resolution,[],[f111,f107])).

fof(f107,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f129,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f33,f127])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f125,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f43,f123])).

fof(f43,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,
    ( ~ spl4_17
    | spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f115,f101,f59,f117])).

fof(f115,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl4_4
    | ~ spl4_14 ),
    inference(resolution,[],[f102,f60])).

fof(f112,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f29,f110])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f108,plain,
    ( spl4_15
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f104,f93,f87,f106])).

fof(f87,plain,
    ( spl4_11
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f93,plain,
    ( spl4_12
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f104,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f88,f94])).

fof(f94,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f88,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f103,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f39,f101])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f99,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,
    ( spl4_12
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f90,f79,f75,f93])).

fof(f75,plain,
    ( spl4_8
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f79,plain,
    ( spl4_9
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f90,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(superposition,[],[f76,f80])).

fof(f80,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f76,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f89,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f30,f87])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f81,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f77,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f69,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f65,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f61,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f57,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (25487)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (25480)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (25487)Refutation not found, incomplete strategy% (25487)------------------------------
% 0.22/0.50  % (25487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25487)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25487)Memory used [KB]: 6012
% 0.22/0.50  % (25487)Time elapsed: 0.085 s
% 0.22/0.50  % (25487)------------------------------
% 0.22/0.50  % (25487)------------------------------
% 0.22/0.50  % (25495)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (25489)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (25495)Refutation not found, incomplete strategy% (25495)------------------------------
% 0.22/0.51  % (25495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25495)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25495)Memory used [KB]: 10490
% 0.22/0.51  % (25495)Time elapsed: 0.095 s
% 0.22/0.51  % (25495)------------------------------
% 0.22/0.51  % (25495)------------------------------
% 0.22/0.51  % (25475)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (25477)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (25481)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (25485)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (25494)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (25478)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (25490)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (25479)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (25488)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (25484)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (25478)Refutation not found, incomplete strategy% (25478)------------------------------
% 0.22/0.52  % (25478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25478)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25478)Memory used [KB]: 10746
% 0.22/0.52  % (25478)Time elapsed: 0.080 s
% 0.22/0.52  % (25478)------------------------------
% 0.22/0.52  % (25478)------------------------------
% 0.22/0.52  % (25485)Refutation not found, incomplete strategy% (25485)------------------------------
% 0.22/0.52  % (25485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25485)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25485)Memory used [KB]: 6012
% 0.22/0.52  % (25485)Time elapsed: 0.093 s
% 0.22/0.52  % (25485)------------------------------
% 0.22/0.52  % (25485)------------------------------
% 0.22/0.52  % (25482)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (25491)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (25486)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (25476)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (25484)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f388,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f65,f69,f77,f81,f89,f95,f99,f103,f108,f112,f119,f125,f129,f133,f137,f142,f150,f161,f165,f175,f179,f190,f198,f209,f216,f231,f237,f253,f262,f284,f305,f312,f317,f369,f387])).
% 0.22/0.53  fof(f387,plain,(
% 0.22/0.53    spl4_32 | ~spl4_3 | ~spl4_37),
% 0.22/0.53    inference(avatar_split_clause,[],[f383,f229,f55,f201])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    spl4_32 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    spl4_37 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.53  fof(f383,plain,(
% 0.22/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_3 | ~spl4_37)),
% 0.22/0.53    inference(forward_demodulation,[],[f56,f230])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl4_37),
% 0.22/0.53    inference(avatar_component_clause,[],[f229])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f55])).
% 0.22/0.53  fof(f369,plain,(
% 0.22/0.53    spl4_37 | ~spl4_6 | ~spl4_33),
% 0.22/0.53    inference(avatar_split_clause,[],[f334,f207,f67,f229])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl4_6 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    spl4_33 <=> v1_xboole_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | (~spl4_6 | ~spl4_33)),
% 0.22/0.53    inference(resolution,[],[f208,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f67])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    v1_xboole_0(sK1) | ~spl4_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f207])).
% 0.22/0.53  fof(f317,plain,(
% 0.22/0.53    ~spl4_14 | ~spl4_41 | spl4_43),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f316])).
% 0.22/0.53  fof(f316,plain,(
% 0.22/0.53    $false | (~spl4_14 | ~spl4_41 | spl4_43)),
% 0.22/0.53    inference(subsumption_resolution,[],[f314,f261])).
% 0.22/0.53  fof(f261,plain,(
% 0.22/0.53    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl4_41),
% 0.22/0.53    inference(avatar_component_clause,[],[f260])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    spl4_41 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl4_14 | spl4_43)),
% 0.22/0.53    inference(resolution,[],[f311,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl4_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl4_14 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl4_43),
% 0.22/0.53    inference(avatar_component_clause,[],[f310])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    spl4_43 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.22/0.53  fof(f312,plain,(
% 0.22/0.53    ~spl4_43 | ~spl4_18 | ~spl4_32 | spl4_42),
% 0.22/0.53    inference(avatar_split_clause,[],[f308,f303,f201,f123,f310])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl4_18 <=> ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    spl4_42 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.22/0.53  fof(f308,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),sK0) | (~spl4_18 | ~spl4_32 | spl4_42)),
% 0.22/0.53    inference(subsumption_resolution,[],[f307,f202])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_32),
% 0.22/0.53    inference(avatar_component_clause,[],[f201])).
% 0.22/0.53  fof(f307,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_18 | spl4_42)),
% 0.22/0.53    inference(superposition,[],[f304,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f123])).
% 0.22/0.53  fof(f304,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl4_42),
% 0.22/0.53    inference(avatar_component_clause,[],[f303])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    ~spl4_42 | spl4_34 | ~spl4_37),
% 0.22/0.53    inference(avatar_split_clause,[],[f293,f229,f214,f303])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    spl4_34 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.53  fof(f293,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl4_34 | ~spl4_37)),
% 0.22/0.53    inference(forward_demodulation,[],[f215,f230])).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | spl4_34),
% 0.22/0.53    inference(avatar_component_clause,[],[f214])).
% 0.22/0.53  fof(f284,plain,(
% 0.22/0.53    spl4_17 | ~spl4_28 | ~spl4_30 | ~spl4_37),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f283])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    $false | (spl4_17 | ~spl4_28 | ~spl4_30 | ~spl4_37)),
% 0.22/0.53    inference(subsumption_resolution,[],[f282,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl4_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    spl4_28 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    ~m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (spl4_17 | ~spl4_30 | ~spl4_37)),
% 0.22/0.53    inference(forward_demodulation,[],[f267,f189])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | ~spl4_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f188])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    spl4_30 <=> k1_xboole_0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.53  fof(f267,plain,(
% 0.22/0.53    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (spl4_17 | ~spl4_37)),
% 0.22/0.53    inference(forward_demodulation,[],[f118,f230])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl4_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    spl4_17 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    spl4_41 | ~spl4_2 | ~spl4_22 | ~spl4_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f219,f185,f140,f51,f260])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    spl4_22 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    spl4_29 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl4_2 | ~spl4_22 | ~spl4_29)),
% 0.22/0.53    inference(subsumption_resolution,[],[f218,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f51])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_22 | ~spl4_29)),
% 0.22/0.53    inference(superposition,[],[f141,f186])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f185])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f140])).
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    spl4_37 | ~spl4_1 | ~spl4_19 | spl4_38),
% 0.22/0.53    inference(avatar_split_clause,[],[f240,f235,f127,f47,f229])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    spl4_19 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    spl4_38 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | (~spl4_1 | ~spl4_19 | spl4_38)),
% 0.22/0.53    inference(subsumption_resolution,[],[f238,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl4_19 | spl4_38)),
% 0.22/0.53    inference(resolution,[],[f236,f128])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) ) | ~spl4_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f127])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl4_38),
% 0.22/0.53    inference(avatar_component_clause,[],[f235])).
% 0.22/0.53  fof(f237,plain,(
% 0.22/0.53    ~spl4_38 | spl4_34 | ~spl4_36),
% 0.22/0.53    inference(avatar_split_clause,[],[f233,f226,f214,f235])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    spl4_36 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl4_34 | ~spl4_36)),
% 0.22/0.53    inference(backward_demodulation,[],[f215,f227])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl4_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f226])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    spl4_36 | spl4_37 | ~spl4_3 | ~spl4_27),
% 0.22/0.53    inference(avatar_split_clause,[],[f181,f173,f55,f229,f226])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    spl4_27 <=> ! [X3,X2] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | (~spl4_3 | ~spl4_27)),
% 0.22/0.53    inference(resolution,[],[f174,f56])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) ) | ~spl4_27),
% 0.22/0.53    inference(avatar_component_clause,[],[f173])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    ~spl4_34 | spl4_4 | ~spl4_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f211,f185,f59,f214])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl4_4 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl4_4 | ~spl4_29)),
% 0.22/0.53    inference(backward_demodulation,[],[f60,f186])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f59])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    spl4_33 | ~spl4_24 | ~spl4_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f199,f196,f148,f207])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl4_24 <=> ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    spl4_31 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    v1_xboole_0(sK1) | (~spl4_24 | ~spl4_31)),
% 0.22/0.53    inference(resolution,[],[f197,f149])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | ~spl4_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f148])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    r1_tarski(sK1,k1_xboole_0) | ~spl4_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f196])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    spl4_31 | ~spl4_1 | ~spl4_30),
% 0.22/0.53    inference(avatar_split_clause,[],[f194,f188,f47,f196])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    r1_tarski(sK1,k1_xboole_0) | (~spl4_1 | ~spl4_30)),
% 0.22/0.53    inference(backward_demodulation,[],[f48,f189])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    spl4_29 | spl4_30 | ~spl4_2 | ~spl4_27),
% 0.22/0.53    inference(avatar_split_clause,[],[f180,f173,f51,f188,f185])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | (~spl4_2 | ~spl4_27)),
% 0.22/0.53    inference(resolution,[],[f174,f52])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    spl4_28 | ~spl4_5 | ~spl4_13 | ~spl4_25),
% 0.22/0.53    inference(avatar_split_clause,[],[f171,f159,f97,f63,f177])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl4_5 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl4_13 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    spl4_25 <=> ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl4_5 | ~spl4_13 | ~spl4_25)),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~r1_tarski(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl4_13 | ~spl4_25)),
% 0.22/0.53    inference(resolution,[],[f160,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl4_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f97])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl4_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f159])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    spl4_27 | ~spl4_21 | ~spl4_26),
% 0.22/0.53    inference(avatar_split_clause,[],[f169,f163,f135,f173])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl4_21 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    spl4_26 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) ) | (~spl4_21 | ~spl4_26)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f166])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) ) | (~spl4_21 | ~spl4_26)),
% 0.22/0.53    inference(superposition,[],[f164,f136])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_21),
% 0.22/0.53    inference(avatar_component_clause,[],[f135])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_26),
% 0.22/0.53    inference(avatar_component_clause,[],[f163])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    spl4_26),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f163])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    spl4_25 | ~spl4_18 | ~spl4_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f155,f140,f123,f159])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl4_18 | ~spl4_22)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f154])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl4_18 | ~spl4_22)),
% 0.22/0.53    inference(superposition,[],[f141,f124])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    spl4_24 | ~spl4_13 | ~spl4_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f138,f131,f97,f148])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    spl4_20 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl4_13 | ~spl4_20)),
% 0.22/0.53    inference(resolution,[],[f132,f98])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl4_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f131])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    spl4_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f140])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl4_21),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f135])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    spl4_20 | ~spl4_15 | ~spl4_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f120,f110,f106,f131])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl4_15 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl4_16 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | (~spl4_15 | ~spl4_16)),
% 0.22/0.53    inference(resolution,[],[f111,f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0) | ~spl4_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) ) | ~spl4_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl4_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f127])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl4_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f123])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(equality_resolution,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ~spl4_17 | spl4_4 | ~spl4_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f115,f101,f59,f117])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | (spl4_4 | ~spl4_14)),
% 0.22/0.53    inference(resolution,[],[f102,f60])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    spl4_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f110])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl4_15 | ~spl4_11 | ~spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f104,f93,f87,f106])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl4_11 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl4_12 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0) | (~spl4_11 | ~spl4_12)),
% 0.22/0.53    inference(resolution,[],[f88,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f93])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) ) | ~spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl4_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f101])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl4_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f97])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl4_12 | ~spl4_8 | ~spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f90,f79,f75,f93])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl4_8 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl4_9 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_8 | ~spl4_9)),
% 0.22/0.53    inference(superposition,[],[f76,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl4_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f75])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl4_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f87])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f44,f79])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f75])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f67])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f63])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f59])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f55])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f23,f51])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f24,f47])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (25484)------------------------------
% 0.22/0.53  % (25484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25484)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (25484)Memory used [KB]: 10746
% 0.22/0.53  % (25484)Time elapsed: 0.104 s
% 0.22/0.53  % (25484)------------------------------
% 0.22/0.53  % (25484)------------------------------
% 0.22/0.53  % (25486)Refutation not found, incomplete strategy% (25486)------------------------------
% 0.22/0.53  % (25486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25486)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25486)Memory used [KB]: 10618
% 0.22/0.53  % (25486)Time elapsed: 0.100 s
% 0.22/0.53  % (25486)------------------------------
% 0.22/0.53  % (25486)------------------------------
% 0.22/0.53  % (25474)Success in time 0.162 s
%------------------------------------------------------------------------------
