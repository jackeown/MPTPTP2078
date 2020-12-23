%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 294 expanded)
%              Number of leaves         :   29 ( 104 expanded)
%              Depth                    :   11
%              Number of atoms          :  511 (1005 expanded)
%              Number of equality atoms :   84 ( 221 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f661,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f99,f109,f114,f124,f133,f139,f144,f195,f204,f229,f243,f347,f362,f368,f372,f415,f423,f585,f660])).

fof(f660,plain,
    ( ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10
    | spl5_37 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10
    | spl5_37 ),
    inference(subsumption_resolution,[],[f655,f91])).

fof(f91,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f655,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl5_6
    | ~ spl5_10
    | spl5_37 ),
    inference(resolution,[],[f625,f113])).

fof(f113,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f625,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl5_10
    | spl5_37 ),
    inference(resolution,[],[f619,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f619,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl5_10
    | spl5_37 ),
    inference(subsumption_resolution,[],[f617,f131])).

fof(f131,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f617,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ v1_relat_1(sK3)
        | ~ v5_relat_1(sK3,X0) )
    | spl5_37 ),
    inference(resolution,[],[f587,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f587,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl5_37 ),
    inference(resolution,[],[f584,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f584,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl5_37
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f585,plain,
    ( ~ spl5_37
    | ~ spl5_1
    | spl5_8
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f483,f201,f130,f121,f84,f582])).

fof(f84,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f121,plain,
    ( spl5_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f201,plain,
    ( spl5_16
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f483,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl5_1
    | spl5_8
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(resolution,[],[f123,f354])).

fof(f354,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r1_tarski(k2_relat_1(sK3),X1) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f265,f203])).

fof(f203,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f265,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f94,f131])).

fof(f94,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK3)
        | ~ r1_tarski(k2_relat_1(sK3),X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f86,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f123,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f423,plain,
    ( ~ spl5_8
    | spl5_15
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl5_8
    | spl5_15
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f385,f192])).

fof(f192,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl5_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f385,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_8
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f380,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f380,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_8
    | ~ spl5_20 ),
    inference(superposition,[],[f122,f275])).

fof(f275,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl5_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f415,plain,
    ( spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f413,f191])).

fof(f191,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f190])).

fof(f413,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f412,f75])).

fof(f412,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f406,f275])).

fof(f406,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(resolution,[],[f398,f119])).

fof(f119,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_7
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f398,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(resolution,[],[f353,f65])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | v1_funct_2(sK3,sK0,X0) )
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f351,f131])).

fof(f351,plain,
    ( ! [X0] :
        ( v1_funct_2(sK3,sK0,X0)
        | ~ v1_relat_1(sK3)
        | ~ v5_relat_1(sK3,X0) )
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(resolution,[],[f349,f55])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | v1_funct_2(sK3,sK0,X0) )
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f128,f203])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | v1_funct_2(sK3,k1_relat_1(sK3),X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_9
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | v1_funct_2(sK3,k1_relat_1(sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f372,plain,
    ( ~ spl5_8
    | ~ spl5_16
    | spl5_25 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_16
    | spl5_25 ),
    inference(subsumption_resolution,[],[f370,f122])).

fof(f370,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_16
    | spl5_25 ),
    inference(subsumption_resolution,[],[f369,f203])).

fof(f369,plain,
    ( sK0 != k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_25 ),
    inference(superposition,[],[f367,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f367,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl5_25
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f368,plain,
    ( ~ spl5_25
    | spl5_7
    | ~ spl5_8
    | spl5_20 ),
    inference(avatar_split_clause,[],[f360,f273,f121,f117,f365])).

fof(f360,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl5_7
    | ~ spl5_8
    | spl5_20 ),
    inference(subsumption_resolution,[],[f359,f122])).

fof(f359,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_7
    | spl5_20 ),
    inference(subsumption_resolution,[],[f125,f274])).

fof(f274,plain,
    ( k1_xboole_0 != sK2
    | spl5_20 ),
    inference(avatar_component_clause,[],[f273])).

fof(f125,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_7 ),
    inference(resolution,[],[f119,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f362,plain,
    ( spl5_13
    | ~ spl5_15
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | spl5_13
    | ~ spl5_15
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f247,f168])).

fof(f168,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK3)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl5_13
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f247,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_15
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f246,f191])).

fof(f246,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f244,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f244,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_19 ),
    inference(resolution,[],[f242,f77])).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f242,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl5_19
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f347,plain,
    ( ~ spl5_13
    | ~ spl5_15
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_15
    | spl5_17 ),
    inference(subsumption_resolution,[],[f256,f228])).

fof(f228,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl5_17
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f256,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f255,f191])).

fof(f255,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f251,f76])).

fof(f251,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_13 ),
    inference(superposition,[],[f169,f63])).

fof(f169,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f243,plain,
    ( spl5_19
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f205,f102,f96,f240])).

fof(f96,plain,
    ( spl5_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f205,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f98,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f98,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f229,plain,
    ( ~ spl5_17
    | ~ spl5_4
    | spl5_16 ),
    inference(avatar_split_clause,[],[f222,f201,f102,f226])).

fof(f222,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ spl5_4
    | spl5_16 ),
    inference(forward_demodulation,[],[f202,f104])).

fof(f202,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f204,plain,
    ( spl5_16
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f198,f141,f111,f201])).

fof(f141,plain,
    ( spl5_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f198,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f196,f113])).

fof(f196,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_11 ),
    inference(superposition,[],[f143,f63])).

fof(f143,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f195,plain,
    ( ~ spl5_4
    | ~ spl5_6
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_6
    | spl5_15 ),
    inference(subsumption_resolution,[],[f153,f192])).

fof(f153,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f149,f76])).

fof(f149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(superposition,[],[f113,f104])).

fof(f144,plain,
    ( spl5_11
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f136,f111,f106,f96,f141])).

fof(f106,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f136,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_3
    | spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f135,f113])).

fof(f135,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3
    | spl5_5 ),
    inference(subsumption_resolution,[],[f100,f108])).

fof(f108,plain,
    ( k1_xboole_0 != sK1
    | spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f98,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f139,plain,
    ( ~ spl5_6
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl5_6
    | spl5_10 ),
    inference(subsumption_resolution,[],[f137,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f137,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_6
    | spl5_10 ),
    inference(resolution,[],[f134,f113])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_10 ),
    inference(resolution,[],[f132,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f132,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( spl5_9
    | ~ spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f93,f84,f130,f127])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | v1_funct_2(sK3,k1_relat_1(sK3),X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f124,plain,
    ( ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f82,f121,f117])).

fof(f82,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_subsumption,[],[f42,f40])).

fof(f40,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f114,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f44,f111])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,
    ( spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f41,f106,f102])).

fof(f41,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f45,f89])).

fof(f45,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f42,f84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (28837)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (28838)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (28826)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (28825)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (28827)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (28830)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (28828)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (28833)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (28829)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (28843)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (28826)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f661,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f87,f92,f99,f109,f114,f124,f133,f139,f144,f195,f204,f229,f243,f347,f362,f368,f372,f415,f423,f585,f660])).
% 0.20/0.49  fof(f660,plain,(
% 0.20/0.49    ~spl5_2 | ~spl5_6 | ~spl5_10 | spl5_37),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f659])).
% 0.20/0.49  fof(f659,plain,(
% 0.20/0.49    $false | (~spl5_2 | ~spl5_6 | ~spl5_10 | spl5_37)),
% 0.20/0.49    inference(subsumption_resolution,[],[f655,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    r1_tarski(sK1,sK2) | ~spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl5_2 <=> r1_tarski(sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f655,plain,(
% 0.20/0.49    ~r1_tarski(sK1,sK2) | (~spl5_6 | ~spl5_10 | spl5_37)),
% 0.20/0.49    inference(resolution,[],[f625,f113])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl5_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.49  fof(f625,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(X0,sK2)) ) | (~spl5_10 | spl5_37)),
% 0.20/0.49    inference(resolution,[],[f619,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f619,plain,(
% 0.20/0.49    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~r1_tarski(X0,sK2)) ) | (~spl5_10 | spl5_37)),
% 0.20/0.49    inference(subsumption_resolution,[],[f617,f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    v1_relat_1(sK3) | ~spl5_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    spl5_10 <=> v1_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.49  fof(f617,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,sK2) | ~v1_relat_1(sK3) | ~v5_relat_1(sK3,X0)) ) | spl5_37),
% 0.20/0.49    inference(resolution,[],[f587,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.49  fof(f587,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | ~r1_tarski(X0,sK2)) ) | spl5_37),
% 0.20/0.49    inference(resolution,[],[f584,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.49  fof(f584,plain,(
% 0.20/0.49    ~r1_tarski(k2_relat_1(sK3),sK2) | spl5_37),
% 0.20/0.49    inference(avatar_component_clause,[],[f582])).
% 0.20/0.49  fof(f582,plain,(
% 0.20/0.49    spl5_37 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.49  fof(f585,plain,(
% 0.20/0.49    ~spl5_37 | ~spl5_1 | spl5_8 | ~spl5_10 | ~spl5_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f483,f201,f130,f121,f84,f582])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl5_1 <=> v1_funct_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl5_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    spl5_16 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.49  fof(f483,plain,(
% 0.20/0.49    ~r1_tarski(k2_relat_1(sK3),sK2) | (~spl5_1 | spl5_8 | ~spl5_10 | ~spl5_16)),
% 0.20/0.49    inference(resolution,[],[f123,f354])).
% 0.20/0.49  fof(f354,plain,(
% 0.20/0.49    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r1_tarski(k2_relat_1(sK3),X1)) ) | (~spl5_1 | ~spl5_10 | ~spl5_16)),
% 0.20/0.49    inference(forward_demodulation,[],[f265,f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK3) | ~spl5_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f201])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    ( ! [X1] : (~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))) ) | (~spl5_1 | ~spl5_10)),
% 0.20/0.49    inference(subsumption_resolution,[],[f94,f131])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f86,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    v1_funct_1(sK3) | ~spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f121])).
% 0.20/0.49  fof(f423,plain,(
% 0.20/0.49    ~spl5_8 | spl5_15 | ~spl5_20),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f422])).
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    $false | (~spl5_8 | spl5_15 | ~spl5_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f385,f192])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl5_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f190])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    spl5_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.49  fof(f385,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl5_8 | ~spl5_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f380,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f380,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl5_8 | ~spl5_20)),
% 0.20/0.49    inference(superposition,[],[f122,f275])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl5_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f273])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    spl5_20 <=> k1_xboole_0 = sK2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f121])).
% 0.20/0.49  fof(f415,plain,(
% 0.20/0.49    spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_15 | ~spl5_16 | ~spl5_20),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f414])).
% 0.20/0.49  fof(f414,plain,(
% 0.20/0.49    $false | (spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_15 | ~spl5_16 | ~spl5_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f413,f191])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl5_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f190])).
% 0.20/0.49  fof(f413,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_16 | ~spl5_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f412,f75])).
% 0.20/0.49  fof(f412,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_16 | ~spl5_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f406,f275])).
% 0.20/0.49  fof(f406,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | (spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_16)),
% 0.20/0.49    inference(resolution,[],[f398,f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ~v1_funct_2(sK3,sK0,sK2) | spl5_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl5_7 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.49  fof(f398,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_2(sK3,sK0,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl5_9 | ~spl5_10 | ~spl5_16)),
% 0.20/0.49    inference(resolution,[],[f353,f65])).
% 0.20/0.49  fof(f353,plain,(
% 0.20/0.49    ( ! [X0] : (~v5_relat_1(sK3,X0) | v1_funct_2(sK3,sK0,X0)) ) | (~spl5_9 | ~spl5_10 | ~spl5_16)),
% 0.20/0.49    inference(subsumption_resolution,[],[f351,f131])).
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_2(sK3,sK0,X0) | ~v1_relat_1(sK3) | ~v5_relat_1(sK3,X0)) ) | (~spl5_9 | ~spl5_16)),
% 0.20/0.49    inference(resolution,[],[f349,f55])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | v1_funct_2(sK3,sK0,X0)) ) | (~spl5_9 | ~spl5_16)),
% 0.20/0.49    inference(forward_demodulation,[],[f128,f203])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | v1_funct_2(sK3,k1_relat_1(sK3),X0)) ) | ~spl5_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl5_9 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | v1_funct_2(sK3,k1_relat_1(sK3),X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.49  fof(f372,plain,(
% 0.20/0.49    ~spl5_8 | ~spl5_16 | spl5_25),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f371])).
% 0.20/0.49  fof(f371,plain,(
% 0.20/0.49    $false | (~spl5_8 | ~spl5_16 | spl5_25)),
% 0.20/0.49    inference(subsumption_resolution,[],[f370,f122])).
% 0.20/0.49  fof(f370,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_16 | spl5_25)),
% 0.20/0.49    inference(subsumption_resolution,[],[f369,f203])).
% 0.20/0.49  fof(f369,plain,(
% 0.20/0.49    sK0 != k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_25),
% 0.20/0.49    inference(superposition,[],[f367,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f367,plain,(
% 0.20/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | spl5_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f365])).
% 0.20/0.49  fof(f365,plain,(
% 0.20/0.49    spl5_25 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.49  fof(f368,plain,(
% 0.20/0.49    ~spl5_25 | spl5_7 | ~spl5_8 | spl5_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f360,f273,f121,f117,f365])).
% 0.20/0.49  fof(f360,plain,(
% 0.20/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | (spl5_7 | ~spl5_8 | spl5_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f359,f122])).
% 0.20/0.49  fof(f359,plain,(
% 0.20/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl5_7 | spl5_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f125,f274])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    k1_xboole_0 != sK2 | spl5_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f273])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_7),
% 0.20/0.49    inference(resolution,[],[f119,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f362,plain,(
% 0.20/0.49    spl5_13 | ~spl5_15 | ~spl5_19),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f361])).
% 0.20/0.49  fof(f361,plain,(
% 0.20/0.49    $false | (spl5_13 | ~spl5_15 | ~spl5_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f247,f168])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK3) | spl5_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f167])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl5_13 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl5_15 | ~spl5_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f246,f191])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl5_19),
% 0.20/0.49    inference(forward_demodulation,[],[f244,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_19),
% 0.20/0.49    inference(resolution,[],[f242,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.49    inference(equality_resolution,[],[f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl5_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f240])).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    spl5_19 <=> v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    ~spl5_13 | ~spl5_15 | spl5_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f346])).
% 0.20/0.49  fof(f346,plain,(
% 0.20/0.49    $false | (~spl5_13 | ~spl5_15 | spl5_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f256,f228])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    k1_xboole_0 != k1_relat_1(sK3) | spl5_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f226])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    spl5_17 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.49  fof(f256,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(sK3) | (~spl5_13 | ~spl5_15)),
% 0.20/0.49    inference(subsumption_resolution,[],[f255,f191])).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3) | ~spl5_13),
% 0.20/0.49    inference(forward_demodulation,[],[f251,f76])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_13),
% 0.20/0.49    inference(superposition,[],[f169,f63])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl5_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f167])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    spl5_19 | ~spl5_3 | ~spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f205,f102,f96,f240])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl5_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    spl5_4 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl5_3 | ~spl5_4)),
% 0.20/0.49    inference(superposition,[],[f98,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | ~spl5_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f102])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl5_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f96])).
% 0.20/0.49  fof(f229,plain,(
% 0.20/0.49    ~spl5_17 | ~spl5_4 | spl5_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f222,f201,f102,f226])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    k1_xboole_0 != k1_relat_1(sK3) | (~spl5_4 | spl5_16)),
% 0.20/0.49    inference(forward_demodulation,[],[f202,f104])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    sK0 != k1_relat_1(sK3) | spl5_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f201])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    spl5_16 | ~spl5_6 | ~spl5_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f198,f141,f111,f201])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    spl5_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK3) | (~spl5_6 | ~spl5_11)),
% 0.20/0.49    inference(subsumption_resolution,[],[f196,f113])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_11),
% 0.20/0.49    inference(superposition,[],[f143,f63])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f141])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~spl5_4 | ~spl5_6 | spl5_15),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    $false | (~spl5_4 | ~spl5_6 | spl5_15)),
% 0.20/0.49    inference(subsumption_resolution,[],[f153,f192])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl5_4 | ~spl5_6)),
% 0.20/0.49    inference(forward_demodulation,[],[f149,f76])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_4 | ~spl5_6)),
% 0.20/0.49    inference(superposition,[],[f113,f104])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    spl5_11 | ~spl5_3 | spl5_5 | ~spl5_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f136,f111,f106,f96,f141])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    spl5_5 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl5_3 | spl5_5 | ~spl5_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f135,f113])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_3 | spl5_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f100,f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | spl5_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f106])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 0.20/0.49    inference(resolution,[],[f98,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ~spl5_6 | spl5_10),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    $false | (~spl5_6 | spl5_10)),
% 0.20/0.49    inference(subsumption_resolution,[],[f137,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl5_6 | spl5_10)),
% 0.20/0.49    inference(resolution,[],[f134,f113])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_10),
% 0.20/0.49    inference(resolution,[],[f132,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ~v1_relat_1(sK3) | spl5_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f130])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    spl5_9 | ~spl5_10 | ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f93,f84,f130,f127])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X0) | v1_funct_2(sK3,k1_relat_1(sK3),X0)) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f86,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ~spl5_7 | ~spl5_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f82,f121,f117])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2)),
% 0.20/0.49    inference(global_subsumption,[],[f42,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.49    inference(ennf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f18])).
% 0.20/0.49  fof(f18,conjecture,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    v1_funct_1(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl5_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f111])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl5_4 | ~spl5_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f106,f102])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f96])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f89])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    r1_tarski(sK1,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f84])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (28826)------------------------------
% 0.20/0.49  % (28826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28826)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (28826)Memory used [KB]: 10874
% 0.20/0.49  % (28826)Time elapsed: 0.058 s
% 0.20/0.49  % (28826)------------------------------
% 0.20/0.49  % (28826)------------------------------
% 0.20/0.49  % (28824)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (28841)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (28822)Success in time 0.14 s
%------------------------------------------------------------------------------
