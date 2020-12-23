%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 252 expanded)
%              Number of leaves         :   40 ( 109 expanded)
%              Depth                    :    7
%              Number of atoms          :  505 ( 871 expanded)
%              Number of equality atoms :   73 ( 120 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f81,f85,f89,f93,f97,f101,f113,f117,f125,f134,f142,f152,f167,f177,f190,f206,f220,f232,f251,f276,f282,f303,f359,f362,f365,f371])).

fof(f371,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_13
    | spl4_55 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_13
    | spl4_55 ),
    inference(subsumption_resolution,[],[f369,f76])).

fof(f76,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f369,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | spl4_3
    | ~ spl4_13
    | spl4_55 ),
    inference(subsumption_resolution,[],[f367,f72])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f367,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3,sK0)
    | ~ spl4_13
    | spl4_55 ),
    inference(resolution,[],[f358,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f358,plain,
    ( ~ r2_hidden(sK3,sK0)
    | spl4_55 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl4_55
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f365,plain,
    ( ~ spl4_6
    | ~ spl4_16
    | spl4_54 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_16
    | spl4_54 ),
    inference(unit_resulting_resolution,[],[f84,f355,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f355,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl4_54 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl4_54
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f84,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f362,plain,
    ( ~ spl4_6
    | ~ spl4_14
    | spl4_53 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_14
    | spl4_53 ),
    inference(unit_resulting_resolution,[],[f84,f352,f116])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f352,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_53 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl4_53
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f359,plain,
    ( ~ spl4_53
    | ~ spl4_54
    | ~ spl4_55
    | ~ spl4_1
    | ~ spl4_26
    | ~ spl4_40
    | spl4_45 ),
    inference(avatar_split_clause,[],[f309,f301,f274,f175,f63,f357,f354,f351])).

fof(f63,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f175,plain,
    ( spl4_26
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f274,plain,
    ( spl4_40
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f301,plain,
    ( spl4_45
  <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f309,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_26
    | ~ spl4_40
    | spl4_45 ),
    inference(forward_demodulation,[],[f308,f275])).

fof(f275,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f274])).

fof(f308,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_26
    | spl4_45 ),
    inference(subsumption_resolution,[],[f307,f64])).

fof(f64,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f307,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_26
    | spl4_45 ),
    inference(trivial_inequality_removal,[],[f306])).

fof(f306,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_26
    | spl4_45 ),
    inference(superposition,[],[f302,f176])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f175])).

% (21990)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f302,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f301])).

fof(f303,plain,
    ( ~ spl4_45
    | ~ spl4_4
    | spl4_8
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f288,f280,f91,f75,f301])).

fof(f91,plain,
    ( spl4_8
  <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f280,plain,
    ( spl4_41
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f288,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ spl4_4
    | spl4_8
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f287,f76])).

fof(f287,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ m1_subset_1(sK3,sK0)
    | spl4_8
    | ~ spl4_41 ),
    inference(superposition,[],[f92,f281])).

fof(f281,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f280])).

fof(f92,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f282,plain,
    ( spl4_41
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f256,f249,f83,f79,f71,f280])).

fof(f79,plain,
    ( spl4_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f249,plain,
    ( spl4_36
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0) )
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f255,f84])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0) )
    | spl4_3
    | ~ spl4_5
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f254,f72])).

fof(f254,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0) )
    | ~ spl4_5
    | ~ spl4_36 ),
    inference(resolution,[],[f250,f80])).

fof(f80,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f249])).

fof(f276,plain,
    ( spl4_40
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f243,f215,f132,f83,f274])).

fof(f132,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f215,plain,
    ( spl4_33
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f243,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f239,f84])).

fof(f239,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_18
    | ~ spl4_33 ),
    inference(superposition,[],[f216,f133])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f216,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f215])).

fof(f251,plain,
    ( spl4_36
    | ~ spl4_1
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f211,f204,f63,f249])).

fof(f204,plain,
    ( spl4_31
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) )
    | ~ spl4_1
    | ~ spl4_31 ),
    inference(resolution,[],[f205,f64])).

fof(f205,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | v1_xboole_0(X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f204])).

fof(f232,plain,
    ( ~ spl4_7
    | spl4_25
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl4_7
    | spl4_25
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f226,f88])).

fof(f88,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_7
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f226,plain,
    ( ~ r1_tarski(k1_xboole_0,o_1_0_mcart_1(k1_xboole_0))
    | spl4_25
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f166,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_34
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f166,plain,
    ( ~ r1_tarski(sK1,o_1_0_mcart_1(sK1))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_25
  <=> r1_tarski(sK1,o_1_0_mcart_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f220,plain,
    ( spl4_33
    | spl4_34
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f202,f188,f83,f79,f218,f215])).

fof(f188,plain,
    ( spl4_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f202,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f199,f84])).

fof(f199,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5
    | ~ spl4_29 ),
    inference(resolution,[],[f189,f80])).

fof(f189,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f188])).

fof(f206,plain,(
    spl4_31 ),
    inference(avatar_split_clause,[],[f56,f204])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f190,plain,(
    spl4_29 ),
    inference(avatar_split_clause,[],[f54,f188])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f177,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f41,f175])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

% (21989)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f167,plain,
    ( ~ spl4_25
    | ~ spl4_9
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f157,f150,f95,f165])).

fof(f95,plain,
    ( spl4_9
  <=> ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f150,plain,
    ( spl4_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f157,plain,
    ( ~ r1_tarski(sK1,o_1_0_mcart_1(sK1))
    | ~ spl4_9
    | ~ spl4_22 ),
    inference(resolution,[],[f151,f96])).

fof(f96,plain,
    ( ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f143,f140,f67,f150])).

fof(f67,plain,
    ( spl4_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f140,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ r1_tarski(sK1,X0) )
    | spl4_2
    | ~ spl4_20 ),
    inference(resolution,[],[f141,f68])).

fof(f68,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( spl4_20
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f130,f111,f99,f140])).

fof(f99,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(resolution,[],[f112,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f134,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f46,f132])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f125,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f48,f123])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f117,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f45,f115])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f113,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f40,f111])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f101,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f44,f99])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f97,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f39,f95])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_mcart_1)).

fof(f93,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f32,f91])).

fof(f32,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

fof(f89,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f85,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f35,f83])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (21986)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (21999)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (22002)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (21994)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (21991)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (21995)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (21994)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (21986)Refutation not found, incomplete strategy% (21986)------------------------------
% 0.21/0.47  % (21986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21986)Memory used [KB]: 10618
% 0.21/0.47  % (21986)Time elapsed: 0.062 s
% 0.21/0.47  % (21986)------------------------------
% 0.21/0.47  % (21986)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f81,f85,f89,f93,f97,f101,f113,f117,f125,f134,f142,f152,f167,f177,f190,f206,f220,f232,f251,f276,f282,f303,f359,f362,f365,f371])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    spl4_3 | ~spl4_4 | ~spl4_13 | spl4_55),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f370])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    $false | (spl4_3 | ~spl4_4 | ~spl4_13 | spl4_55)),
% 0.21/0.48    inference(subsumption_resolution,[],[f369,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    m1_subset_1(sK3,sK0) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl4_4 <=> m1_subset_1(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,sK0) | (spl4_3 | ~spl4_13 | spl4_55)),
% 0.21/0.48    inference(subsumption_resolution,[],[f367,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl4_3 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | ~m1_subset_1(sK3,sK0) | (~spl4_13 | spl4_55)),
% 0.21/0.48    inference(resolution,[],[f358,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl4_13 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    ~r2_hidden(sK3,sK0) | spl4_55),
% 0.21/0.48    inference(avatar_component_clause,[],[f357])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    spl4_55 <=> r2_hidden(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    ~spl4_6 | ~spl4_16 | spl4_54),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f363])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    $false | (~spl4_6 | ~spl4_16 | spl4_54)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f84,f355,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl4_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    ~v5_relat_1(sK2,sK1) | spl4_54),
% 0.21/0.48    inference(avatar_component_clause,[],[f354])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    spl4_54 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    ~spl4_6 | ~spl4_14 | spl4_53),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f360])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    $false | (~spl4_6 | ~spl4_14 | spl4_53)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f84,f352,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl4_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl4_53),
% 0.21/0.48    inference(avatar_component_clause,[],[f351])).
% 0.21/0.48  fof(f351,plain,(
% 0.21/0.48    spl4_53 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    ~spl4_53 | ~spl4_54 | ~spl4_55 | ~spl4_1 | ~spl4_26 | ~spl4_40 | spl4_45),
% 0.21/0.48    inference(avatar_split_clause,[],[f309,f301,f274,f175,f63,f357,f354,f351])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl4_1 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    spl4_26 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.48  fof(f274,plain,(
% 0.21/0.48    spl4_40 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    spl4_45 <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    ~r2_hidden(sK3,sK0) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_26 | ~spl4_40 | spl4_45)),
% 0.21/0.48    inference(forward_demodulation,[],[f308,f275])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | ~spl4_40),
% 0.21/0.48    inference(avatar_component_clause,[],[f274])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    ~v5_relat_1(sK2,sK1) | ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_26 | spl4_45)),
% 0.21/0.48    inference(subsumption_resolution,[],[f307,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_26 | spl4_45)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f306])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3) | ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_26 | spl4_45)),
% 0.21/0.48    inference(superposition,[],[f302,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f175])).
% 0.21/0.48  % (21990)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | spl4_45),
% 0.21/0.48    inference(avatar_component_clause,[],[f301])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    ~spl4_45 | ~spl4_4 | spl4_8 | ~spl4_41),
% 0.21/0.48    inference(avatar_split_clause,[],[f288,f280,f91,f75,f301])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl4_8 <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    spl4_41 <=> ! [X0] : (~m1_subset_1(X0,sK0) | k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | (~spl4_4 | spl4_8 | ~spl4_41)),
% 0.21/0.48    inference(subsumption_resolution,[],[f287,f76])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | ~m1_subset_1(sK3,sK0) | (spl4_8 | ~spl4_41)),
% 0.21/0.48    inference(superposition,[],[f92,f281])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_41),
% 0.21/0.48    inference(avatar_component_clause,[],[f280])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) | spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    spl4_41 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_36),
% 0.21/0.48    inference(avatar_split_clause,[],[f256,f249,f83,f79,f71,f280])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl4_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    spl4_36 <=> ! [X1,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,sK0) | k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0)) ) | (spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_36)),
% 0.21/0.48    inference(subsumption_resolution,[],[f255,f84])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0)) ) | (spl4_3 | ~spl4_5 | ~spl4_36)),
% 0.21/0.48    inference(subsumption_resolution,[],[f254,f72])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_funct_1(sK2,X0) = k3_funct_2(sK0,sK1,sK2,X0)) ) | (~spl4_5 | ~spl4_36)),
% 0.21/0.48    inference(resolution,[],[f250,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2)) ) | ~spl4_36),
% 0.21/0.48    inference(avatar_component_clause,[],[f249])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    spl4_40 | ~spl4_6 | ~spl4_18 | ~spl4_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f243,f215,f132,f83,f274])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl4_18 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    spl4_33 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | (~spl4_6 | ~spl4_18 | ~spl4_33)),
% 0.21/0.48    inference(subsumption_resolution,[],[f239,f84])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_18 | ~spl4_33)),
% 0.21/0.48    inference(superposition,[],[f216,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f132])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f215])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    spl4_36 | ~spl4_1 | ~spl4_31),
% 0.21/0.48    inference(avatar_split_clause,[],[f211,f204,f63,f249])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    spl4_31 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2)) ) | (~spl4_1 | ~spl4_31)),
% 0.21/0.48    inference(resolution,[],[f205,f64])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) ) | ~spl4_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f204])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~spl4_7 | spl4_25 | ~spl4_34),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f231])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    $false | (~spl4_7 | spl4_25 | ~spl4_34)),
% 0.21/0.48    inference(subsumption_resolution,[],[f226,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl4_7 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,o_1_0_mcart_1(k1_xboole_0)) | (spl4_25 | ~spl4_34)),
% 0.21/0.48    inference(backward_demodulation,[],[f166,f219])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl4_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl4_34 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ~r1_tarski(sK1,o_1_0_mcart_1(sK1)) | spl4_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f165])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    spl4_25 <=> r1_tarski(sK1,o_1_0_mcart_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    spl4_33 | spl4_34 | ~spl4_5 | ~spl4_6 | ~spl4_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f202,f188,f83,f79,f218,f215])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    spl4_29 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_5 | ~spl4_6 | ~spl4_29)),
% 0.21/0.48    inference(subsumption_resolution,[],[f199,f84])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_5 | ~spl4_29)),
% 0.21/0.48    inference(resolution,[],[f189,f80])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f188])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl4_31),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f204])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl4_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f188])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl4_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f175])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.48  % (21989)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ~spl4_25 | ~spl4_9 | ~spl4_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f157,f150,f95,f165])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl4_9 <=> ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl4_22 <=> ! [X0] : (~m1_subset_1(X0,sK1) | ~r1_tarski(sK1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~r1_tarski(sK1,o_1_0_mcart_1(sK1)) | (~spl4_9 | ~spl4_22)),
% 0.21/0.48    inference(resolution,[],[f151,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(o_1_0_mcart_1(X0),X0)) ) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~r1_tarski(sK1,X0)) ) | ~spl4_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f150])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl4_22 | spl4_2 | ~spl4_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f143,f140,f67,f150])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl4_2 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl4_20 <=> ! [X1,X0] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~r1_tarski(sK1,X0)) ) | (spl4_2 | ~spl4_20)),
% 0.21/0.48    inference(resolution,[],[f141,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X0,X1)) ) | ~spl4_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl4_20 | ~spl4_10 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f130,f111,f99,f140])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl4_10 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X0,X1)) ) | (~spl4_10 | ~spl4_13)),
% 0.21/0.48    inference(resolution,[],[f112,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f132])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl4_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f123])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f115])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f111])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f99])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f95])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(o_1_0_mcart_1(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_mcart_1)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f91])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f87])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f83])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f79])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f75])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_subset_1(sK3,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f71])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f67])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f63])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21994)------------------------------
% 0.21/0.48  % (21994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21994)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21994)Memory used [KB]: 10746
% 0.21/0.48  % (21994)Time elapsed: 0.065 s
% 0.21/0.48  % (21994)------------------------------
% 0.21/0.48  % (21994)------------------------------
% 0.21/0.48  % (21984)Success in time 0.124 s
%------------------------------------------------------------------------------
