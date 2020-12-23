%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 356 expanded)
%              Number of leaves         :   49 ( 167 expanded)
%              Depth                    :    7
%              Number of atoms          :  624 (1146 expanded)
%              Number of equality atoms :   90 ( 191 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f652,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f97,f101,f105,f114,f131,f135,f139,f147,f151,f159,f163,f171,f184,f198,f228,f232,f235,f259,f266,f290,f328,f329,f333,f366,f377,f430,f441,f455,f499,f541,f566,f593,f651])).

fof(f651,plain,
    ( ~ spl6_34
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_45
    | ~ spl6_53
    | spl6_65
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(avatar_split_clause,[],[f601,f591,f564,f439,f364,f304,f137,f133,f99,f71,f223])).

% (12931)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f223,plain,
    ( spl6_34
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f71,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f99,plain,
    ( spl6_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f133,plain,
    ( spl6_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f137,plain,
    ( spl6_17
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f304,plain,
    ( spl6_45
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f364,plain,
    ( spl6_53
  <=> r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f439,plain,
    ( spl6_65
  <=> m1_subset_1(sK5(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f564,plain,
    ( spl6_68
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f591,plain,
    ( spl6_72
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

% (12929)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f601,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_45
    | ~ spl6_53
    | spl6_65
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f600,f555])).

fof(f555,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_45
    | spl6_65 ),
    inference(backward_demodulation,[],[f452,f305])).

fof(f305,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f304])).

fof(f452,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_8
    | spl6_65 ),
    inference(resolution,[],[f440,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f440,plain,
    ( ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | spl6_65 ),
    inference(avatar_component_clause,[],[f439])).

fof(f600,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_53
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(backward_demodulation,[],[f372,f599])).

fof(f599,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_16
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f594,f565])).

fof(f565,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f564])).

fof(f594,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_16
    | ~ spl6_72 ),
    inference(superposition,[],[f592,f134])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f592,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f591])).

fof(f372,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_17
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f368,f72])).

fof(f72,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f368,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_17
    | ~ spl6_53 ),
    inference(resolution,[],[f365,f138])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        | ~ v1_funct_1(X2)
        | r2_hidden(X0,k1_relat_1(X2))
        | ~ v1_relat_1(X2) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f137])).

fof(f365,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f364])).

fof(f593,plain,
    ( spl6_72
    | ~ spl6_25
    | ~ spl6_40
    | ~ spl6_45
    | ~ spl6_67 ),
    inference(avatar_split_clause,[],[f562,f497,f304,f264,f169,f591])).

fof(f169,plain,
    ( spl6_25
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f264,plain,
    ( spl6_40
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f497,plain,
    ( spl6_67
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f562,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_25
    | ~ spl6_40
    | ~ spl6_45
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f559,f544])).

fof(f544,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_40
    | ~ spl6_45 ),
    inference(backward_demodulation,[],[f265,f305])).

fof(f265,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f264])).

fof(f559,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_25
    | ~ spl6_67 ),
    inference(resolution,[],[f498,f170])).

fof(f170,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(X2,k1_xboole_0,X1)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f169])).

fof(f498,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f497])).

fof(f566,plain,
    ( spl6_68
    | ~ spl6_40
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f544,f304,f264,f564])).

fof(f541,plain,
    ( ~ spl6_5
    | ~ spl6_44
    | spl6_54 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_44
    | spl6_54 ),
    inference(subsumption_resolution,[],[f522,f88])).

fof(f88,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_5
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f522,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK5(sK4,sK2,k1_xboole_0),sK4))
    | ~ spl6_44
    | spl6_54 ),
    inference(backward_demodulation,[],[f376,f302])).

fof(f302,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl6_44
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f376,plain,
    ( ~ r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4))
    | spl6_54 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl6_54
  <=> r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f499,plain,
    ( spl6_67
    | ~ spl6_39
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f484,f304,f257,f497])).

fof(f257,plain,
    ( spl6_39
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f484,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_39
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f258,f305])).

fof(f258,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f257])).

fof(f455,plain,
    ( ~ spl6_8
    | ~ spl6_47
    | spl6_65 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_47
    | spl6_65 ),
    inference(subsumption_resolution,[],[f452,f327])).

fof(f327,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl6_47
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f441,plain,
    ( ~ spl6_65
    | ~ spl6_6
    | ~ spl6_35
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f433,f428,f226,f91,f439])).

fof(f91,plain,
    ( spl6_6
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK0)
        | ~ r2_hidden(X5,sK2)
        | sK4 != k1_funct_1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f226,plain,
    ( spl6_35
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f428,plain,
    ( spl6_63
  <=> sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f433,plain,
    ( ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_6
    | ~ spl6_35
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f432,f227])).

fof(f227,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f226])).

fof(f432,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_6
    | ~ spl6_63 ),
    inference(trivial_inequality_removal,[],[f431])).

fof(f431,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_6
    | ~ spl6_63 ),
    inference(superposition,[],[f92,f429])).

fof(f429,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f428])).

fof(f92,plain,
    ( ! [X5] :
        ( sK4 != k1_funct_1(sK3,X5)
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f430,plain,
    ( ~ spl6_34
    | spl6_63
    | ~ spl6_1
    | ~ spl6_20
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f371,f364,f149,f71,f428,f223])).

fof(f149,plain,
    ( spl6_20
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_funct_1(X2,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f371,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_20
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f367,f72])).

fof(f367,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_20
    | ~ spl6_53 ),
    inference(resolution,[],[f365,f150])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        | ~ v1_funct_1(X2)
        | k1_funct_1(X2,X0) = X1
        | ~ v1_relat_1(X2) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f377,plain,
    ( ~ spl6_54
    | ~ spl6_9
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f370,f364,f103,f375])).

fof(f103,plain,
    ( spl6_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f370,plain,
    ( ~ r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4))
    | ~ spl6_9
    | ~ spl6_53 ),
    inference(resolution,[],[f365,f104])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f366,plain,
    ( ~ spl6_34
    | spl6_53
    | ~ spl6_22
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f201,f196,f157,f364,f223])).

fof(f157,plain,
    ( spl6_22
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f196,plain,
    ( spl6_30
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f201,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_22
    | ~ spl6_30 ),
    inference(resolution,[],[f197,f158])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        | ~ v1_relat_1(X2) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f157])).

fof(f197,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f196])).

fof(f333,plain,
    ( ~ spl6_40
    | spl6_44
    | spl6_45
    | ~ spl6_28
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f260,f257,f182,f304,f301,f264])).

fof(f182,plain,
    ( spl6_28
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

% (12930)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f260,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_28
    | ~ spl6_39 ),
    inference(resolution,[],[f258,f183])).

fof(f183,plain,
    ( ! [X2,X0] :
        ( ~ v1_funct_2(X2,X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f182])).

fof(f329,plain,
    ( spl6_37
    | spl6_38
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f291,f230,f79,f75,f248,f245])).

fof(f245,plain,
    ( spl6_37
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f248,plain,
    ( spl6_38
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f75,plain,
    ( spl6_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f79,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f230,plain,
    ( spl6_36
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f291,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f276,f80])).

fof(f80,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f276,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_2
    | ~ spl6_36 ),
    inference(resolution,[],[f76,f231])).

fof(f231,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f230])).

fof(f76,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f328,plain,
    ( ~ spl6_34
    | spl6_47
    | ~ spl6_19
    | ~ spl6_30
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f307,f288,f196,f145,f326,f223])).

fof(f145,plain,
    ( spl6_19
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f288,plain,
    ( spl6_43
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f307,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_19
    | ~ spl6_30
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f202,f289])).

fof(f289,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f288])).

fof(f202,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(resolution,[],[f197,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
        | ~ v1_relat_1(X2) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f290,plain,
    ( spl6_43
    | ~ spl6_3
    | ~ spl6_16
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f284,f245,f133,f79,f288])).

fof(f284,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_3
    | ~ spl6_16
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f280,f80])).

fof(f280,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16
    | ~ spl6_37 ),
    inference(superposition,[],[f246,f134])).

fof(f246,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f245])).

fof(f266,plain,
    ( spl6_40
    | ~ spl6_3
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f252,f248,f79,f264])).

fof(f252,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f80,f249])).

fof(f249,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f248])).

fof(f259,plain,
    ( spl6_39
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f251,f248,f75,f257])).

fof(f251,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f76,f249])).

fof(f235,plain,
    ( ~ spl6_3
    | ~ spl6_7
    | ~ spl6_11
    | spl6_34 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_11
    | spl6_34 ),
    inference(unit_resulting_resolution,[],[f96,f80,f224,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f224,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_34 ),
    inference(avatar_component_clause,[],[f223])).

fof(f96,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_7
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f232,plain,(
    spl6_36 ),
    inference(avatar_split_clause,[],[f56,f230])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f228,plain,
    ( ~ spl6_34
    | spl6_35
    | ~ spl6_15
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f203,f196,f129,f226,f223])).

fof(f129,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK5(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f203,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl6_15
    | ~ spl6_30 ),
    inference(resolution,[],[f197,f130])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | r2_hidden(sK5(X0,X1,X2),X1)
        | ~ v1_relat_1(X2) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f198,plain,
    ( spl6_30
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f194,f161,f83,f79,f196])).

fof(f83,plain,
    ( spl6_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f161,plain,
    ( spl6_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f194,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f190,f80])).

fof(f190,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(superposition,[],[f84,f162])).

fof(f162,plain,
    ( ! [X2,X0,X3,X1] :
        ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f161])).

fof(f84,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f184,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f66,f182])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f171,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f64,f169])).

fof(f64,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f163,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f63,f161])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f159,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f47,f157])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f151,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f58,f149])).

% (12928)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (12934)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f147,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f46,f145])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f139,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f57,f137])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f135,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f50,f133])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f131,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f48,f129])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f114,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f41,f112])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f105,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f45,f103])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f101,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f43,f99])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f97,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f93,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f35,f91])).

fof(f35,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f89,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f40,f87])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f85,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f38,f75])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:15:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (12927)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (12933)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (12919)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (12926)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (12923)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (12932)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (12922)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (12936)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (12924)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (12921)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (12917)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (12917)Refutation not found, incomplete strategy% (12917)------------------------------
% 0.22/0.51  % (12917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12917)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12917)Memory used [KB]: 10618
% 0.22/0.51  % (12917)Time elapsed: 0.091 s
% 0.22/0.51  % (12917)------------------------------
% 0.22/0.51  % (12917)------------------------------
% 0.22/0.52  % (12925)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (12937)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (12916)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12926)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (12935)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f652,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f97,f101,f105,f114,f131,f135,f139,f147,f151,f159,f163,f171,f184,f198,f228,f232,f235,f259,f266,f290,f328,f329,f333,f366,f377,f430,f441,f455,f499,f541,f566,f593,f651])).
% 0.22/0.52  fof(f651,plain,(
% 0.22/0.52    ~spl6_34 | ~spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_17 | ~spl6_45 | ~spl6_53 | spl6_65 | ~spl6_68 | ~spl6_72),
% 0.22/0.52    inference(avatar_split_clause,[],[f601,f591,f564,f439,f364,f304,f137,f133,f99,f71,f223])).
% 0.22/0.52  % (12931)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    spl6_34 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl6_1 <=> v1_funct_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    spl6_8 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    spl6_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    spl6_17 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.52  fof(f304,plain,(
% 0.22/0.52    spl6_45 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.22/0.52  fof(f364,plain,(
% 0.22/0.52    spl6_53 <=> r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.22/0.52  fof(f439,plain,(
% 0.22/0.52    spl6_65 <=> m1_subset_1(sK5(sK4,sK2,sK3),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.22/0.52  fof(f564,plain,(
% 0.22/0.52    spl6_68 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.22/0.52  fof(f591,plain,(
% 0.22/0.52    spl6_72 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 0.22/0.52  % (12929)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f601,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_8 | ~spl6_16 | ~spl6_17 | ~spl6_45 | ~spl6_53 | spl6_65 | ~spl6_68 | ~spl6_72)),
% 0.22/0.52    inference(subsumption_resolution,[],[f600,f555])).
% 0.22/0.52  fof(f555,plain,(
% 0.22/0.52    ~r2_hidden(sK5(sK4,sK2,sK3),k1_xboole_0) | (~spl6_8 | ~spl6_45 | spl6_65)),
% 0.22/0.52    inference(backward_demodulation,[],[f452,f305])).
% 0.22/0.52  fof(f305,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~spl6_45),
% 0.22/0.52    inference(avatar_component_clause,[],[f304])).
% 0.22/0.52  fof(f452,plain,(
% 0.22/0.52    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | (~spl6_8 | spl6_65)),
% 0.22/0.52    inference(resolution,[],[f440,f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl6_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f99])).
% 0.22/0.52  fof(f440,plain,(
% 0.22/0.52    ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | spl6_65),
% 0.22/0.52    inference(avatar_component_clause,[],[f439])).
% 0.22/0.52  fof(f600,plain,(
% 0.22/0.52    r2_hidden(sK5(sK4,sK2,sK3),k1_xboole_0) | ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_16 | ~spl6_17 | ~spl6_53 | ~spl6_68 | ~spl6_72)),
% 0.22/0.52    inference(backward_demodulation,[],[f372,f599])).
% 0.22/0.52  fof(f599,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK3) | (~spl6_16 | ~spl6_68 | ~spl6_72)),
% 0.22/0.52    inference(subsumption_resolution,[],[f594,f565])).
% 0.22/0.52  fof(f565,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_68),
% 0.22/0.52    inference(avatar_component_clause,[],[f564])).
% 0.22/0.52  fof(f594,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_16 | ~spl6_72)),
% 0.22/0.52    inference(superposition,[],[f592,f134])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f133])).
% 0.22/0.52  fof(f592,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl6_72),
% 0.22/0.52    inference(avatar_component_clause,[],[f591])).
% 0.22/0.52  fof(f372,plain,(
% 0.22/0.52    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_17 | ~spl6_53)),
% 0.22/0.52    inference(subsumption_resolution,[],[f368,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    v1_funct_1(sK3) | ~spl6_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f71])).
% 0.22/0.52  fof(f368,plain,(
% 0.22/0.52    ~v1_funct_1(sK3) | r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_17 | ~spl6_53)),
% 0.22/0.52    inference(resolution,[],[f365,f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) ) | ~spl6_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f137])).
% 0.22/0.52  fof(f365,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~spl6_53),
% 0.22/0.52    inference(avatar_component_clause,[],[f364])).
% 0.22/0.52  fof(f593,plain,(
% 0.22/0.52    spl6_72 | ~spl6_25 | ~spl6_40 | ~spl6_45 | ~spl6_67),
% 0.22/0.52    inference(avatar_split_clause,[],[f562,f497,f304,f264,f169,f591])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl6_25 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    spl6_40 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.22/0.52  fof(f497,plain,(
% 0.22/0.52    spl6_67 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 0.22/0.52  fof(f562,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_25 | ~spl6_40 | ~spl6_45 | ~spl6_67)),
% 0.22/0.52    inference(subsumption_resolution,[],[f559,f544])).
% 0.22/0.52  fof(f544,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_40 | ~spl6_45)),
% 0.22/0.52    inference(backward_demodulation,[],[f265,f305])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_40),
% 0.22/0.52    inference(avatar_component_clause,[],[f264])).
% 0.22/0.52  fof(f559,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_25 | ~spl6_67)),
% 0.22/0.52    inference(resolution,[],[f498,f170])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl6_25),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f498,plain,(
% 0.22/0.52    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl6_67),
% 0.22/0.52    inference(avatar_component_clause,[],[f497])).
% 0.22/0.52  fof(f566,plain,(
% 0.22/0.52    spl6_68 | ~spl6_40 | ~spl6_45),
% 0.22/0.52    inference(avatar_split_clause,[],[f544,f304,f264,f564])).
% 0.22/0.52  fof(f541,plain,(
% 0.22/0.52    ~spl6_5 | ~spl6_44 | spl6_54),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f540])).
% 0.22/0.52  fof(f540,plain,(
% 0.22/0.52    $false | (~spl6_5 | ~spl6_44 | spl6_54)),
% 0.22/0.52    inference(subsumption_resolution,[],[f522,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl6_5 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.52  fof(f522,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,k4_tarski(sK5(sK4,sK2,k1_xboole_0),sK4)) | (~spl6_44 | spl6_54)),
% 0.22/0.52    inference(backward_demodulation,[],[f376,f302])).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    k1_xboole_0 = sK3 | ~spl6_44),
% 0.22/0.52    inference(avatar_component_clause,[],[f301])).
% 0.22/0.52  fof(f301,plain,(
% 0.22/0.52    spl6_44 <=> k1_xboole_0 = sK3),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.22/0.52  fof(f376,plain,(
% 0.22/0.52    ~r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4)) | spl6_54),
% 0.22/0.52    inference(avatar_component_clause,[],[f375])).
% 0.22/0.52  fof(f375,plain,(
% 0.22/0.52    spl6_54 <=> r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.22/0.52  fof(f499,plain,(
% 0.22/0.52    spl6_67 | ~spl6_39 | ~spl6_45),
% 0.22/0.52    inference(avatar_split_clause,[],[f484,f304,f257,f497])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    spl6_39 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.22/0.52  fof(f484,plain,(
% 0.22/0.52    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_39 | ~spl6_45)),
% 0.22/0.52    inference(forward_demodulation,[],[f258,f305])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl6_39),
% 0.22/0.52    inference(avatar_component_clause,[],[f257])).
% 0.22/0.52  fof(f455,plain,(
% 0.22/0.52    ~spl6_8 | ~spl6_47 | spl6_65),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f454])).
% 0.22/0.52  fof(f454,plain,(
% 0.22/0.52    $false | (~spl6_8 | ~spl6_47 | spl6_65)),
% 0.22/0.52    inference(subsumption_resolution,[],[f452,f327])).
% 0.22/0.52  fof(f327,plain,(
% 0.22/0.52    r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~spl6_47),
% 0.22/0.52    inference(avatar_component_clause,[],[f326])).
% 0.22/0.52  fof(f326,plain,(
% 0.22/0.52    spl6_47 <=> r2_hidden(sK5(sK4,sK2,sK3),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.22/0.52  fof(f441,plain,(
% 0.22/0.52    ~spl6_65 | ~spl6_6 | ~spl6_35 | ~spl6_63),
% 0.22/0.52    inference(avatar_split_clause,[],[f433,f428,f226,f91,f439])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl6_6 <=> ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    spl6_35 <=> r2_hidden(sK5(sK4,sK2,sK3),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.52  fof(f428,plain,(
% 0.22/0.52    spl6_63 <=> sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.22/0.52  fof(f433,plain,(
% 0.22/0.52    ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | (~spl6_6 | ~spl6_35 | ~spl6_63)),
% 0.22/0.52    inference(subsumption_resolution,[],[f432,f227])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~spl6_35),
% 0.22/0.52    inference(avatar_component_clause,[],[f226])).
% 0.22/0.52  fof(f432,plain,(
% 0.22/0.52    ~r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | (~spl6_6 | ~spl6_63)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f431])).
% 0.22/0.52  fof(f431,plain,(
% 0.22/0.52    sK4 != sK4 | ~r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | (~spl6_6 | ~spl6_63)),
% 0.22/0.52    inference(superposition,[],[f92,f429])).
% 0.22/0.52  fof(f429,plain,(
% 0.22/0.52    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~spl6_63),
% 0.22/0.52    inference(avatar_component_clause,[],[f428])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) ) | ~spl6_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f91])).
% 0.22/0.52  fof(f430,plain,(
% 0.22/0.52    ~spl6_34 | spl6_63 | ~spl6_1 | ~spl6_20 | ~spl6_53),
% 0.22/0.52    inference(avatar_split_clause,[],[f371,f364,f149,f71,f428,f223])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    spl6_20 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.52  fof(f371,plain,(
% 0.22/0.52    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_20 | ~spl6_53)),
% 0.22/0.52    inference(subsumption_resolution,[],[f367,f72])).
% 0.22/0.52  fof(f367,plain,(
% 0.22/0.52    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl6_20 | ~spl6_53)),
% 0.22/0.52    inference(resolution,[],[f365,f150])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) ) | ~spl6_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f149])).
% 0.22/0.52  fof(f377,plain,(
% 0.22/0.52    ~spl6_54 | ~spl6_9 | ~spl6_53),
% 0.22/0.52    inference(avatar_split_clause,[],[f370,f364,f103,f375])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl6_9 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.52  fof(f370,plain,(
% 0.22/0.52    ~r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4)) | (~spl6_9 | ~spl6_53)),
% 0.22/0.52    inference(resolution,[],[f365,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl6_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f103])).
% 0.22/0.52  fof(f366,plain,(
% 0.22/0.52    ~spl6_34 | spl6_53 | ~spl6_22 | ~spl6_30),
% 0.22/0.52    inference(avatar_split_clause,[],[f201,f196,f157,f364,f223])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    spl6_22 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    spl6_30 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | (~spl6_22 | ~spl6_30)),
% 0.22/0.52    inference(resolution,[],[f197,f158])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) ) | ~spl6_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f157])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl6_30),
% 0.22/0.52    inference(avatar_component_clause,[],[f196])).
% 0.22/0.52  fof(f333,plain,(
% 0.22/0.52    ~spl6_40 | spl6_44 | spl6_45 | ~spl6_28 | ~spl6_39),
% 0.22/0.52    inference(avatar_split_clause,[],[f260,f257,f182,f304,f301,f264])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    spl6_28 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.52  % (12930)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_28 | ~spl6_39)),
% 0.22/0.52    inference(resolution,[],[f258,f183])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | ~spl6_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f182])).
% 0.22/0.52  fof(f329,plain,(
% 0.22/0.52    spl6_37 | spl6_38 | ~spl6_2 | ~spl6_3 | ~spl6_36),
% 0.22/0.52    inference(avatar_split_clause,[],[f291,f230,f79,f75,f248,f245])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    spl6_37 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    spl6_38 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl6_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    spl6_36 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.52  fof(f291,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl6_2 | ~spl6_3 | ~spl6_36)),
% 0.22/0.52    inference(subsumption_resolution,[],[f276,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f276,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_2 | ~spl6_36)),
% 0.22/0.52    inference(resolution,[],[f76,f231])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_36),
% 0.22/0.52    inference(avatar_component_clause,[],[f230])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,sK1) | ~spl6_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f328,plain,(
% 0.22/0.52    ~spl6_34 | spl6_47 | ~spl6_19 | ~spl6_30 | ~spl6_43),
% 0.22/0.52    inference(avatar_split_clause,[],[f307,f288,f196,f145,f326,f223])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    spl6_19 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.52  fof(f288,plain,(
% 0.22/0.52    spl6_43 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.22/0.52  fof(f307,plain,(
% 0.22/0.52    r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~v1_relat_1(sK3) | (~spl6_19 | ~spl6_30 | ~spl6_43)),
% 0.22/0.52    inference(backward_demodulation,[],[f202,f289])).
% 0.22/0.52  fof(f289,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK3) | ~spl6_43),
% 0.22/0.52    inference(avatar_component_clause,[],[f288])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_19 | ~spl6_30)),
% 0.22/0.52    inference(resolution,[],[f197,f146])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) ) | ~spl6_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f145])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    spl6_43 | ~spl6_3 | ~spl6_16 | ~spl6_37),
% 0.22/0.52    inference(avatar_split_clause,[],[f284,f245,f133,f79,f288])).
% 0.22/0.52  fof(f284,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK3) | (~spl6_3 | ~spl6_16 | ~spl6_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f280,f80])).
% 0.22/0.52  fof(f280,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_16 | ~spl6_37)),
% 0.22/0.52    inference(superposition,[],[f246,f134])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_37),
% 0.22/0.52    inference(avatar_component_clause,[],[f245])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    spl6_40 | ~spl6_3 | ~spl6_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f252,f248,f79,f264])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_3 | ~spl6_38)),
% 0.22/0.52    inference(backward_demodulation,[],[f80,f249])).
% 0.22/0.52  fof(f249,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl6_38),
% 0.22/0.52    inference(avatar_component_clause,[],[f248])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    spl6_39 | ~spl6_2 | ~spl6_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f251,f248,f75,f257])).
% 0.22/0.52  fof(f251,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl6_2 | ~spl6_38)),
% 0.22/0.52    inference(backward_demodulation,[],[f76,f249])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    ~spl6_3 | ~spl6_7 | ~spl6_11 | spl6_34),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f233])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    $false | (~spl6_3 | ~spl6_7 | ~spl6_11 | spl6_34)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f96,f80,f224,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl6_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f112])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl6_11 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | spl6_34),
% 0.22/0.52    inference(avatar_component_clause,[],[f223])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl6_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl6_7 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    spl6_36),
% 0.22/0.52    inference(avatar_split_clause,[],[f56,f230])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    ~spl6_34 | spl6_35 | ~spl6_15 | ~spl6_30),
% 0.22/0.52    inference(avatar_split_clause,[],[f203,f196,f129,f226,f223])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    spl6_15 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | (~spl6_15 | ~spl6_30)),
% 0.22/0.52    inference(resolution,[],[f197,f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2)) ) | ~spl6_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f129])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    spl6_30 | ~spl6_3 | ~spl6_4 | ~spl6_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f194,f161,f83,f79,f196])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl6_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    spl6_23 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_3 | ~spl6_4 | ~spl6_23)),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f80])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_4 | ~spl6_23)),
% 0.22/0.52    inference(superposition,[],[f84,f162])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f161])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl6_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f83])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    spl6_28),
% 0.22/0.52    inference(avatar_split_clause,[],[f66,f182])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    spl6_25),
% 0.22/0.52    inference(avatar_split_clause,[],[f64,f169])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    spl6_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f63,f161])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl6_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f157])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl6_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f58,f149])).
% 0.22/0.53  % (12928)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (12934)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl6_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f46,f145])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    spl6_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f137])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl6_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f133])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    spl6_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f129])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    spl6_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f112])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f103])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f99])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f95])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl6_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f91])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.53    inference(negated_conjecture,[],[f15])).
% 0.22/0.53  fof(f15,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f87])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f83])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f79])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f75])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f71])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (12926)------------------------------
% 0.22/0.53  % (12926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12926)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (12926)Memory used [KB]: 10874
% 0.22/0.53  % (12926)Time elapsed: 0.105 s
% 0.22/0.53  % (12926)------------------------------
% 0.22/0.53  % (12926)------------------------------
% 0.22/0.53  % (12915)Success in time 0.171 s
%------------------------------------------------------------------------------
