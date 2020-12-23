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
% DateTime   : Thu Dec  3 13:07:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 328 expanded)
%              Number of leaves         :   48 ( 152 expanded)
%              Depth                    :    7
%              Number of atoms          :  588 (1099 expanded)
%              Number of equality atoms :   45 (  72 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f82,f86,f90,f94,f98,f105,f108,f112,f120,f124,f128,f133,f140,f144,f148,f166,f170,f192,f198,f208,f216,f222,f224,f238,f245,f248,f253,f262,f274,f297,f318,f326,f361,f385,f395])).

fof(f395,plain,
    ( spl6_2
    | ~ spl6_8
    | ~ spl6_51 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | spl6_2
    | ~ spl6_8
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f386,f93])).

fof(f93,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f386,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_2
    | ~ spl6_51 ),
    inference(backward_demodulation,[],[f69,f357])).

fof(f357,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl6_51
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f69,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f385,plain,
    ( ~ spl6_35
    | ~ spl6_14
    | ~ spl6_38
    | ~ spl6_44
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f367,f359,f295,f260,f118,f240])).

fof(f240,plain,
    ( spl6_35
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f118,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f260,plain,
    ( spl6_38
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f295,plain,
    ( spl6_44
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f359,plain,
    ( spl6_52
  <=> sK0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f367,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_14
    | ~ spl6_38
    | ~ spl6_44
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f364,f340])).

fof(f340,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl6_38
    | ~ spl6_44 ),
    inference(resolution,[],[f261,f296])).

fof(f296,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f295])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | ~ r1_tarski(X0,k1_relat_1(sK2)) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f260])).

fof(f364,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_14
    | ~ spl6_52 ),
    inference(superposition,[],[f119,f360])).

fof(f360,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f359])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f361,plain,
    ( spl6_51
    | spl6_52
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_34
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f258,f251,f236,f88,f84,f64,f359,f356])).

fof(f64,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( spl6_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f88,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f236,plain,
    ( spl6_34
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f251,plain,
    ( spl6_37
  <=> ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f258,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_34
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f257,f65])).

fof(f65,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f257,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_34
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f256,f89])).

fof(f89,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f256,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ spl6_6
    | ~ spl6_34
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f254,f85])).

fof(f85,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f254,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ spl6_34
    | ~ spl6_37 ),
    inference(superposition,[],[f252,f237])).

fof(f237,plain,
    ( ! [X2,X0,X1] :
        ( k8_relset_1(X0,X1,X2,X1) = X0
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X2) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f236])).

fof(f252,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f251])).

fof(f326,plain,
    ( ~ spl6_35
    | ~ spl6_1
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f325,f316,f196,f138,f64,f240])).

fof(f138,plain,
    ( spl6_18
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f196,plain,
    ( spl6_29
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f316,plain,
    ( spl6_47
  <=> ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f325,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f324,f65])).

fof(f324,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f322,f197])).

fof(f197,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f196])).

fof(f322,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_18
    | ~ spl6_47 ),
    inference(resolution,[],[f317,f139])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0) )
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f316])).

fof(f318,plain,
    ( ~ spl6_35
    | spl6_47
    | ~ spl6_19
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f268,f214,f142,f316,f240])).

fof(f142,plain,
    ( spl6_19
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f214,plain,
    ( spl6_32
  <=> ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK3),X0)
        | ~ r1_tarski(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_19
    | ~ spl6_32 ),
    inference(resolution,[],[f215,f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f142])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK3),X0)
        | ~ r1_tarski(X0,sK4) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f214])).

fof(f297,plain,
    ( spl6_44
    | ~ spl6_5
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f280,f272,f80,f295])).

fof(f80,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f272,plain,
    ( spl6_39
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f280,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl6_5
    | ~ spl6_39 ),
    inference(resolution,[],[f273,f81])).

fof(f81,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f272])).

fof(f274,plain,
    ( spl6_39
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f135,f122,f110,f96,f272])).

fof(f96,plain,
    ( spl6_9
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f110,plain,
    ( spl6_12
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f122,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f134,f97])).

fof(f97,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(resolution,[],[f123,f111])).

fof(f111,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f262,plain,
    ( spl6_38
    | ~ spl6_17
    | spl6_36 ),
    inference(avatar_split_clause,[],[f249,f243,f131,f260])).

fof(f131,plain,
    ( spl6_17
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f243,plain,
    ( spl6_36
  <=> r1_tarski(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(sK3,X0) )
    | ~ spl6_17
    | spl6_36 ),
    inference(resolution,[],[f244,f132])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f131])).

fof(f244,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f243])).

fof(f253,plain,
    ( spl6_37
    | ~ spl6_7
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f193,f168,f88,f251])).

fof(f168,plain,
    ( spl6_25
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f193,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl6_7
    | ~ spl6_25 ),
    inference(resolution,[],[f169,f89])).

fof(f169,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f168])).

fof(f248,plain,
    ( ~ spl6_7
    | ~ spl6_16
    | spl6_35 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_16
    | spl6_35 ),
    inference(unit_resulting_resolution,[],[f89,f241,f127])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f241,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f240])).

fof(f245,plain,
    ( ~ spl6_35
    | ~ spl6_36
    | ~ spl6_1
    | ~ spl6_27
    | spl6_29
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f228,f206,f196,f185,f64,f243,f240])).

fof(f185,plain,
    ( spl6_27
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f206,plain,
    ( spl6_30
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r1_tarski(X0,k1_relat_1(X2))
        | ~ r1_tarski(k9_relat_1(X2,X0),X1)
        | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f228,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_27
    | spl6_29
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f227,f221])).

fof(f221,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f185])).

fof(f227,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_29
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f225,f65])).

fof(f225,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ v1_relat_1(sK2)
    | spl6_29
    | ~ spl6_30 ),
    inference(resolution,[],[f223,f207])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k10_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ r1_tarski(X0,k1_relat_1(X2))
        | ~ r1_tarski(k9_relat_1(X2,X0),X1)
        | ~ v1_relat_1(X2) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f206])).

fof(f223,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f196])).

fof(f238,plain,(
    spl6_34 ),
    inference(avatar_split_clause,[],[f54,f236])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

% (18068)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f224,plain,
    ( ~ spl6_29
    | ~ spl6_7
    | spl6_11
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f217,f168,f103,f88,f196])).

fof(f103,plain,
    ( spl6_11
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f217,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_7
    | spl6_11
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f107,f193])).

fof(f107,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f222,plain,
    ( spl6_27
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f220,f190,f100,f185])).

fof(f100,plain,
    ( spl6_10
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f190,plain,
    ( spl6_28
  <=> ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f220,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f101,f191])).

fof(f191,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f190])).

fof(f101,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f216,plain,
    ( spl6_32
    | ~ spl6_7
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f182,f164,f146,f88,f214])).

fof(f146,plain,
    ( spl6_20
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f164,plain,
    ( spl6_24
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK3),X0)
        | ~ r1_tarski(X0,sK4) )
    | ~ spl6_7
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f147,f178])).

fof(f178,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl6_7
    | ~ spl6_24 ),
    inference(resolution,[],[f165,f89])).

fof(f165,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f164])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X0)
        | ~ r1_tarski(X0,sK4) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f208,plain,(
    spl6_30 ),
    inference(avatar_split_clause,[],[f56,f206])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f198,plain,
    ( spl6_29
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f194,f168,f103,f88,f196])).

fof(f194,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_25 ),
    inference(backward_demodulation,[],[f104,f193])).

fof(f104,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f192,plain,
    ( spl6_28
    | ~ spl6_7
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f178,f164,f88,f190])).

fof(f170,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f59,f168])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f166,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f58,f164])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f148,plain,
    ( spl6_20
    | spl6_10
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f136,f131,f100,f146])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X0) )
    | spl6_10
    | ~ spl6_17 ),
    inference(resolution,[],[f132,f106])).

fof(f106,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f144,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f52,f142])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f140,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f47,f138])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f133,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f57,f131])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f128,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f53,f126])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f46,f122])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f120,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f45,f118])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f112,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f60,f110])).

fof(f60,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f108,plain,
    ( ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f35,f103,f100])).

fof(f35,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(f105,plain,
    ( spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f34,f103,f100])).

fof(f34,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f94,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f43,f92])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f40,f88])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f41,f68])).

fof(f41,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f38,f64])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (18066)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (18058)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (18072)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (18075)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (18057)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (18076)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (18066)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (18060)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f396,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f66,f70,f82,f86,f90,f94,f98,f105,f108,f112,f120,f124,f128,f133,f140,f144,f148,f166,f170,f192,f198,f208,f216,f222,f224,f238,f245,f248,f253,f262,f274,f297,f318,f326,f361,f385,f395])).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    spl6_2 | ~spl6_8 | ~spl6_51),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f394])).
% 0.21/0.49  fof(f394,plain,(
% 0.21/0.49    $false | (spl6_2 | ~spl6_8 | ~spl6_51)),
% 0.21/0.49    inference(subsumption_resolution,[],[f386,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl6_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f386,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | (spl6_2 | ~spl6_51)),
% 0.21/0.49    inference(backward_demodulation,[],[f69,f357])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl6_51),
% 0.21/0.49    inference(avatar_component_clause,[],[f356])).
% 0.21/0.49  fof(f356,plain,(
% 0.21/0.49    spl6_51 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1) | spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl6_2 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    ~spl6_35 | ~spl6_14 | ~spl6_38 | ~spl6_44 | ~spl6_52),
% 0.21/0.49    inference(avatar_split_clause,[],[f367,f359,f295,f260,f118,f240])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    spl6_35 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl6_14 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    spl6_38 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(sK3,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    spl6_44 <=> r1_tarski(sK3,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.49  fof(f359,plain,(
% 0.21/0.49    spl6_52 <=> sK0 = k10_relat_1(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | (~spl6_14 | ~spl6_38 | ~spl6_44 | ~spl6_52)),
% 0.21/0.49    inference(subsumption_resolution,[],[f364,f340])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k1_relat_1(sK2)) | (~spl6_38 | ~spl6_44)),
% 0.21/0.49    inference(resolution,[],[f261,f296])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    r1_tarski(sK3,sK0) | ~spl6_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f295])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK3,X0) | ~r1_tarski(X0,k1_relat_1(sK2))) ) | ~spl6_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f260])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl6_14 | ~spl6_52)),
% 0.21/0.49    inference(superposition,[],[f119,f360])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | ~spl6_52),
% 0.21/0.49    inference(avatar_component_clause,[],[f359])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    spl6_51 | spl6_52 | ~spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_34 | ~spl6_37),
% 0.21/0.49    inference(avatar_split_clause,[],[f258,f251,f236,f88,f84,f64,f359,f356])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl6_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    spl6_34 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    spl6_37 <=> ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | k1_xboole_0 = sK1 | (~spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_34 | ~spl6_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f257,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | (~spl6_6 | ~spl6_7 | ~spl6_34 | ~spl6_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f256,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | (~spl6_6 | ~spl6_34 | ~spl6_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f254,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    sK0 = k10_relat_1(sK2,sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | (~spl6_34 | ~spl6_37)),
% 0.21/0.49    inference(superposition,[],[f252,f237])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_1(X2)) ) | ~spl6_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f236])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl6_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f251])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    ~spl6_35 | ~spl6_1 | ~spl6_18 | ~spl6_29 | ~spl6_47),
% 0.21/0.49    inference(avatar_split_clause,[],[f325,f316,f196,f138,f64,f240])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl6_18 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl6_29 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    spl6_47 <=> ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | (~spl6_1 | ~spl6_18 | ~spl6_29 | ~spl6_47)),
% 0.21/0.49    inference(subsumption_resolution,[],[f324,f65])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_18 | ~spl6_29 | ~spl6_47)),
% 0.21/0.49    inference(subsumption_resolution,[],[f322,f197])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl6_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f196])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_18 | ~spl6_47)),
% 0.21/0.49    inference(resolution,[],[f317,f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0)) ) | ~spl6_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f316])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ~spl6_35 | spl6_47 | ~spl6_19 | ~spl6_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f268,f214,f142,f316,f240])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl6_19 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    spl6_32 <=> ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK3),X0) | ~r1_tarski(X0,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0) | ~v1_relat_1(sK2)) ) | (~spl6_19 | ~spl6_32)),
% 0.21/0.49    inference(resolution,[],[f215,f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) ) | ~spl6_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f142])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK3),X0) | ~r1_tarski(X0,sK4)) ) | ~spl6_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f214])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    spl6_44 | ~spl6_5 | ~spl6_39),
% 0.21/0.49    inference(avatar_split_clause,[],[f280,f272,f80,f295])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    spl6_39 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    r1_tarski(sK3,sK0) | (~spl6_5 | ~spl6_39)),
% 0.21/0.49    inference(resolution,[],[f273,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | ~spl6_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f272])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    spl6_39 | ~spl6_9 | ~spl6_12 | ~spl6_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f135,f122,f110,f96,f272])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl6_9 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl6_12 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl6_15 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl6_9 | ~spl6_12 | ~spl6_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f134,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl6_12 | ~spl6_15)),
% 0.21/0.49    inference(resolution,[],[f123,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl6_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f110])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    spl6_38 | ~spl6_17 | spl6_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f249,f243,f131,f260])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl6_17 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    spl6_36 <=> r1_tarski(sK3,k1_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(sK3,X0)) ) | (~spl6_17 | spl6_36)),
% 0.21/0.49    inference(resolution,[],[f244,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) ) | ~spl6_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f131])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k1_relat_1(sK2)) | spl6_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f243])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl6_37 | ~spl6_7 | ~spl6_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f193,f168,f88,f251])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl6_25 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) ) | (~spl6_7 | ~spl6_25)),
% 0.21/0.49    inference(resolution,[],[f169,f89])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl6_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f168])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    ~spl6_7 | ~spl6_16 | spl6_35),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    $false | (~spl6_7 | ~spl6_16 | spl6_35)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f89,f241,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl6_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | spl6_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f240])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    ~spl6_35 | ~spl6_36 | ~spl6_1 | ~spl6_27 | spl6_29 | ~spl6_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f228,f206,f196,f185,f64,f243,f240])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl6_27 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    spl6_30 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl6_1 | ~spl6_27 | spl6_29 | ~spl6_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f227,f221])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl6_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~v1_relat_1(sK2) | (~spl6_1 | spl6_29 | ~spl6_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f225,f65])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~r1_tarski(sK3,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~v1_relat_1(sK2) | (spl6_29 | ~spl6_30)),
% 0.21/0.49    inference(resolution,[],[f223,f207])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) ) | ~spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f206])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl6_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f196])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    spl6_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f236])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  % (18068)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~spl6_29 | ~spl6_7 | spl6_11 | ~spl6_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f217,f168,f103,f88,f196])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl6_11 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl6_7 | spl6_11 | ~spl6_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f107,f193])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f103])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl6_27 | ~spl6_10 | ~spl6_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f220,f190,f100,f185])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl6_10 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    spl6_28 <=> ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_10 | ~spl6_28)),
% 0.21/0.49    inference(forward_demodulation,[],[f101,f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl6_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f190])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl6_32 | ~spl6_7 | ~spl6_20 | ~spl6_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f182,f164,f146,f88,f214])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl6_20 <=> ! [X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl6_24 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK3),X0) | ~r1_tarski(X0,sK4)) ) | (~spl6_7 | ~spl6_20 | ~spl6_24)),
% 0.21/0.49    inference(backward_demodulation,[],[f147,f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)) ) | (~spl6_7 | ~spl6_24)),
% 0.21/0.49    inference(resolution,[],[f165,f89])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) ) | ~spl6_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f164])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X0) | ~r1_tarski(X0,sK4)) ) | ~spl6_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl6_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f206])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    spl6_29 | ~spl6_7 | ~spl6_11 | ~spl6_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f194,f168,f103,f88,f196])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl6_7 | ~spl6_11 | ~spl6_25)),
% 0.21/0.49    inference(backward_demodulation,[],[f104,f193])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f103])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    spl6_28 | ~spl6_7 | ~spl6_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f178,f164,f88,f190])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl6_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f168])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    spl6_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f164])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl6_20 | spl6_10 | ~spl6_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f136,f131,f100,f146])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X0)) ) | (spl6_10 | ~spl6_17)),
% 0.21/0.49    inference(resolution,[],[f132,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl6_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f142])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl6_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f138])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl6_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f131])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl6_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f126])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl6_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f122])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f118])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f110])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ~spl6_10 | ~spl6_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f103,f100])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl6_10 | spl6_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f103,f100])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f96])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f92])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f88])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f84])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f80])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f68])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f64])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18066)------------------------------
% 0.21/0.49  % (18066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18066)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18066)Memory used [KB]: 10746
% 0.21/0.49  % (18066)Time elapsed: 0.068 s
% 0.21/0.49  % (18066)------------------------------
% 0.21/0.49  % (18066)------------------------------
% 0.21/0.49  % (18056)Success in time 0.133 s
%------------------------------------------------------------------------------
