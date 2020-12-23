%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 185 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :    6
%              Number of atoms          :  333 ( 564 expanded)
%              Number of equality atoms :   36 (  71 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f49,f57,f73,f85,f90,f94,f98,f102,f107,f113,f118,f122,f131,f139,f145,f162,f180,f195,f207,f213])).

fof(f213,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | ~ spl4_15
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_15
    | spl4_35 ),
    inference(subsumption_resolution,[],[f211,f40])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f211,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_15
    | spl4_35 ),
    inference(subsumption_resolution,[],[f209,f48])).

fof(f48,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_4
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f209,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_15
    | spl4_35 ),
    inference(resolution,[],[f206,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f206,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl4_35
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f207,plain,
    ( ~ spl4_35
    | spl4_1
    | ~ spl4_20
    | spl4_33 ),
    inference(avatar_split_clause,[],[f198,f193,f116,f35,f205])).

fof(f35,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f116,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f193,plain,
    ( spl4_33
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f198,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | spl4_1
    | ~ spl4_20
    | spl4_33 ),
    inference(subsumption_resolution,[],[f197,f36])).

fof(f36,plain,
    ( sK0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f197,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_20
    | spl4_33 ),
    inference(resolution,[],[f194,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r2_hidden(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f116])).

fof(f194,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( ~ spl4_33
    | ~ spl4_16
    | spl4_30 ),
    inference(avatar_split_clause,[],[f185,f178,f96,f193])).

fof(f96,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ r2_xboole_0(X0,X1)
        | r2_hidden(sK3(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f178,plain,
    ( spl4_30
  <=> r2_hidden(sK3(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f185,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl4_16
    | spl4_30 ),
    inference(resolution,[],[f179,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X1)
        | ~ r2_xboole_0(X0,X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f96])).

fof(f179,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( ~ spl4_30
    | spl4_1
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f167,f160,f39,f35,f178])).

fof(f160,plain,
    ( spl4_27
  <=> ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(sK3(sK1,X0),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f167,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f165,f36])).

fof(f165,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | sK0 = sK1
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(resolution,[],[f161,f40])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ r2_hidden(sK3(sK1,X0),sK0)
        | sK1 = X0 )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl4_27
    | ~ spl4_4
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f151,f143,f92,f47,f160])).

fof(f143,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(sK1,X0),sK0)
        | sK1 = X0
        | ~ r2_hidden(sK1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f151,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(sK3(sK1,X0),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl4_4
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f150,f48])).

fof(f150,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(sK3(sK1,X0),sK0)
        | v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(resolution,[],[f144,f93])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k1_zfmisc_1(X0))
        | sK1 = X0
        | ~ r2_hidden(sK3(sK1,X0),sK0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl4_24
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f141,f137,f55,f143])).

fof(f55,plain,
    ( spl4_6
  <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f137,plain,
    ( spl4_23
  <=> ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | k3_tarski(X1) = sK1
        | ~ r2_hidden(sK3(sK1,k3_tarski(X1)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,X0),sK0)
        | sK1 = X0
        | ~ r2_hidden(sK1,k1_zfmisc_1(X0)) )
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(superposition,[],[f138,f56])).

fof(f56,plain,
    ( ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f138,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK1,k3_tarski(X1)),sK0)
        | k3_tarski(X1) = sK1
        | ~ r2_hidden(sK1,X1) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl4_23
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f133,f129,f88,f137])).

fof(f88,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f129,plain,
    ( spl4_22
  <=> ! [X1,X2] :
        ( k3_tarski(X1) = X2
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(sK3(X2,k3_tarski(X1)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f133,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | k3_tarski(X1) = sK1
        | ~ r2_hidden(sK3(sK1,k3_tarski(X1)),sK0) )
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(resolution,[],[f130,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f88])).

fof(f130,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK3(X2,k3_tarski(X1)),X2)
        | ~ r2_hidden(X2,X1)
        | k3_tarski(X1) = X2 )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,
    ( spl4_22
    | ~ spl4_17
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f124,f120,f100,f129])).

fof(f100,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f120,plain,
    ( spl4_21
  <=> ! [X3,X2] :
        ( k3_tarski(X3) = X2
        | r2_xboole_0(X2,k3_tarski(X3))
        | ~ r2_hidden(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f124,plain,
    ( ! [X2,X1] :
        ( k3_tarski(X1) = X2
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(sK3(X2,k3_tarski(X1)),X2) )
    | ~ spl4_17
    | ~ spl4_21 ),
    inference(resolution,[],[f121,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_hidden(sK3(X0,X1),X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f100])).

fof(f121,plain,
    ( ! [X2,X3] :
        ( r2_xboole_0(X2,k3_tarski(X3))
        | k3_tarski(X3) = X2
        | ~ r2_hidden(X2,X3) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl4_21
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f109,f105,f83,f120])).

fof(f83,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | r1_tarski(X0,k3_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f105,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f109,plain,
    ( ! [X2,X3] :
        ( k3_tarski(X3) = X2
        | r2_xboole_0(X2,k3_tarski(X3))
        | ~ r2_hidden(X2,X3) )
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(resolution,[],[f106,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f105])).

fof(f118,plain,
    ( spl4_20
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f114,f111,f105,f116])).

fof(f111,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( r1_tarski(X1,X0)
        | ~ r2_hidden(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(resolution,[],[f112,f106])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,X0)
        | ~ r2_hidden(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f103,f83,f55,f111])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,X0)
        | ~ r2_hidden(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(superposition,[],[f84,f56])).

fof(f107,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f29,f105])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f102,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f31,f100])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f98,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f30,f96])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f94,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f25,f92])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f90,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f86,f71,f43,f88])).

fof(f43,plain,
    ( spl4_3
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,sK0)
        | r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f71,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) )
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK0)
        | r2_hidden(X2,sK1) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f85,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f26,f83])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f73,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f19,f55])).

fof(f19,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f49,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f45,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f43])).

fof(f15,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:13:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (7126)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (7126)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f37,f41,f45,f49,f57,f73,f85,f90,f94,f98,f102,f107,f113,f118,f122,f131,f139,f145,f162,f180,f195,f207,f213])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    ~spl4_2 | ~spl4_4 | ~spl4_15 | spl4_35),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f212])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    $false | (~spl4_2 | ~spl4_4 | ~spl4_15 | spl4_35)),
% 0.20/0.49    inference(subsumption_resolution,[],[f211,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl4_4 | ~spl4_15 | spl4_35)),
% 0.20/0.49    inference(subsumption_resolution,[],[f209,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl4_4 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    v1_xboole_0(k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl4_15 | spl4_35)),
% 0.20/0.49    inference(resolution,[],[f206,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) ) | ~spl4_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl4_15 <=> ! [X1,X0] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | spl4_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f205])).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    spl4_35 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    ~spl4_35 | spl4_1 | ~spl4_20 | spl4_33),
% 0.20/0.49    inference(avatar_split_clause,[],[f198,f193,f116,f35,f205])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl4_1 <=> sK0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl4_20 <=> ! [X1,X0] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    spl4_33 <=> r2_xboole_0(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | (spl4_1 | ~spl4_20 | spl4_33)),
% 0.20/0.49    inference(subsumption_resolution,[],[f197,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    sK0 != sK1 | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f35])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    sK0 = sK1 | ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | (~spl4_20 | spl4_33)),
% 0.20/0.49    inference(resolution,[],[f194,f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_zfmisc_1(X1))) ) | ~spl4_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f116])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    ~r2_xboole_0(sK1,sK0) | spl4_33),
% 0.20/0.49    inference(avatar_component_clause,[],[f193])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~spl4_33 | ~spl4_16 | spl4_30),
% 0.20/0.49    inference(avatar_split_clause,[],[f185,f178,f96,f193])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl4_16 <=> ! [X1,X0] : (~r2_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    spl4_30 <=> r2_hidden(sK3(sK1,sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    ~r2_xboole_0(sK1,sK0) | (~spl4_16 | spl4_30)),
% 0.20/0.49    inference(resolution,[],[f179,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | ~r2_xboole_0(X0,X1)) ) | ~spl4_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f96])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK1,sK0),sK0) | spl4_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f178])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ~spl4_30 | spl4_1 | ~spl4_2 | ~spl4_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f167,f160,f39,f35,f178])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl4_27 <=> ! [X0] : (sK1 = X0 | ~r2_hidden(sK3(sK1,X0),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK1,sK0),sK0) | (spl4_1 | ~spl4_2 | ~spl4_27)),
% 0.20/0.49    inference(subsumption_resolution,[],[f165,f36])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK1,sK0),sK0) | sK0 = sK1 | (~spl4_2 | ~spl4_27)),
% 0.20/0.49    inference(resolution,[],[f161,f40])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(sK1,X0),sK0) | sK1 = X0) ) | ~spl4_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f160])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    spl4_27 | ~spl4_4 | ~spl4_15 | ~spl4_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f151,f143,f92,f47,f160])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl4_24 <=> ! [X0] : (~r2_hidden(sK3(sK1,X0),sK0) | sK1 = X0 | ~r2_hidden(sK1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    ( ! [X0] : (sK1 = X0 | ~r2_hidden(sK3(sK1,X0),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | (~spl4_4 | ~spl4_15 | ~spl4_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f150,f48])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X0] : (sK1 = X0 | ~r2_hidden(sK3(sK1,X0),sK0) | v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | (~spl4_15 | ~spl4_24)),
% 0.20/0.49    inference(resolution,[],[f144,f93])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK1,k1_zfmisc_1(X0)) | sK1 = X0 | ~r2_hidden(sK3(sK1,X0),sK0)) ) | ~spl4_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f143])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    spl4_24 | ~spl4_6 | ~spl4_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f141,f137,f55,f143])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl4_6 <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl4_23 <=> ! [X1] : (~r2_hidden(sK1,X1) | k3_tarski(X1) = sK1 | ~r2_hidden(sK3(sK1,k3_tarski(X1)),sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK3(sK1,X0),sK0) | sK1 = X0 | ~r2_hidden(sK1,k1_zfmisc_1(X0))) ) | (~spl4_6 | ~spl4_23)),
% 0.20/0.49    inference(superposition,[],[f138,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) ) | ~spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f55])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(sK3(sK1,k3_tarski(X1)),sK0) | k3_tarski(X1) = sK1 | ~r2_hidden(sK1,X1)) ) | ~spl4_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f137])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl4_23 | ~spl4_14 | ~spl4_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f133,f129,f88,f137])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl4_14 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl4_22 <=> ! [X1,X2] : (k3_tarski(X1) = X2 | ~r2_hidden(X2,X1) | ~r2_hidden(sK3(X2,k3_tarski(X1)),X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(sK1,X1) | k3_tarski(X1) = sK1 | ~r2_hidden(sK3(sK1,k3_tarski(X1)),sK0)) ) | (~spl4_14 | ~spl4_22)),
% 0.20/0.49    inference(resolution,[],[f130,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl4_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f88])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r2_hidden(sK3(X2,k3_tarski(X1)),X2) | ~r2_hidden(X2,X1) | k3_tarski(X1) = X2) ) | ~spl4_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f129])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl4_22 | ~spl4_17 | ~spl4_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f124,f120,f100,f129])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    spl4_17 <=> ! [X1,X0] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK3(X0,X1),X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl4_21 <=> ! [X3,X2] : (k3_tarski(X3) = X2 | r2_xboole_0(X2,k3_tarski(X3)) | ~r2_hidden(X2,X3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k3_tarski(X1) = X2 | ~r2_hidden(X2,X1) | ~r2_hidden(sK3(X2,k3_tarski(X1)),X2)) ) | (~spl4_17 | ~spl4_21)),
% 0.20/0.49    inference(resolution,[],[f121,f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK3(X0,X1),X0)) ) | ~spl4_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f100])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X2,X3] : (r2_xboole_0(X2,k3_tarski(X3)) | k3_tarski(X3) = X2 | ~r2_hidden(X2,X3)) ) | ~spl4_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f120])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    spl4_21 | ~spl4_13 | ~spl4_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f109,f105,f83,f120])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl4_13 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl4_18 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k3_tarski(X3) = X2 | r2_xboole_0(X2,k3_tarski(X3)) | ~r2_hidden(X2,X3)) ) | (~spl4_13 | ~spl4_18)),
% 0.20/0.49    inference(resolution,[],[f106,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) ) | ~spl4_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f83])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl4_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    spl4_20 | ~spl4_18 | ~spl4_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f114,f111,f105,f116])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl4_19 <=> ! [X1,X0] : (r1_tarski(X1,X0) | ~r2_hidden(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | X0 = X1 | r2_xboole_0(X0,X1)) ) | (~spl4_18 | ~spl4_19)),
% 0.20/0.49    inference(resolution,[],[f112,f106])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,k1_zfmisc_1(X0))) ) | ~spl4_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f111])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl4_19 | ~spl4_6 | ~spl4_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f103,f83,f55,f111])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,k1_zfmisc_1(X0))) ) | (~spl4_6 | ~spl4_13)),
% 0.20/0.49    inference(superposition,[],[f84,f56])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl4_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f105])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    spl4_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f100])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK3(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    spl4_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f96])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl4_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f92])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl4_14 | ~spl4_3 | ~spl4_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f86,f71,f43,f88])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    spl4_3 <=> ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl4_10 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) ) | (~spl4_3 | ~spl4_10)),
% 0.20/0.49    inference(resolution,[],[f72,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) ) | ~spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f43])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) ) | ~spl4_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl4_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f83])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl4_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f71])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f24,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f19,f55])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f18,f47])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f15,f43])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f16,f39])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f35])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    sK0 != sK1),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (7126)------------------------------
% 0.20/0.49  % (7126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7126)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (7126)Memory used [KB]: 10618
% 0.20/0.49  % (7126)Time elapsed: 0.081 s
% 0.20/0.49  % (7126)------------------------------
% 0.20/0.49  % (7126)------------------------------
% 0.20/0.49  % (7110)Success in time 0.129 s
%------------------------------------------------------------------------------
