%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 166 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  291 ( 475 expanded)
%              Number of equality atoms :   46 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f79,f83,f87,f99,f103,f108,f112,f122,f126,f156,f171,f186,f234])).

fof(f234,plain,
    ( ~ spl2_5
    | ~ spl2_7
    | ~ spl2_21
    | ~ spl2_24 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_21
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f232,f78])).

fof(f78,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_5
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f232,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_21
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f230,f86])).

fof(f86,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_7
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f230,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)))
    | ~ spl2_21
    | ~ spl2_24 ),
    inference(superposition,[],[f185,f170])).

fof(f170,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl2_21
  <=> k1_xboole_0 = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f185,plain,
    ( ! [X0] : k5_xboole_0(X0,k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X0))) != X0
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl2_24
  <=> ! [X0] : k5_xboole_0(X0,k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X0))) != X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f186,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f50,f184])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X0))) != X0 ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f49,plain,(
    ! [X0] : k1_ordinal1(X0) = k5_xboole_0(X0,k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X0))) ),
    inference(definition_unfolding,[],[f39,f48,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f39,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f34,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f171,plain,
    ( spl2_21
    | spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f166,f153,f106,f67,f57,f168])).

fof(f57,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f67,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f106,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f153,plain,
    ( spl2_19
  <=> k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f166,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f165,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f165,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f162,f59])).

fof(f59,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f162,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | v1_xboole_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f156,plain,
    ( spl2_19
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f128,f115,f81,f153])).

fof(f81,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f115,plain,
    ( spl2_14
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f128,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(resolution,[],[f117,f82])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f81])).

% (2336)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f117,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f126,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | spl2_15 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | spl2_15 ),
    inference(subsumption_resolution,[],[f124,f59])).

fof(f124,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_10
    | spl2_15 ),
    inference(subsumption_resolution,[],[f123,f69])).

fof(f123,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_10
    | spl2_15 ),
    inference(resolution,[],[f121,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f121,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl2_15
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f122,plain,
    ( spl2_14
    | ~ spl2_15
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f113,f110,f72,f119,f115])).

fof(f72,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f110,plain,
    ( spl2_13
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f113,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(resolution,[],[f111,f74])).

fof(f74,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f104,f101,f62,f110])).

fof(f62,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f101,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f104,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_subset_1(X0,sK0) )
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f102,f64])).

fof(f64,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_subset_1(X1,X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f54,f106])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f103,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f55,f101])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f42,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f99,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f47,f97])).

% (2335)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f87,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f51,f85])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f83,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f79,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f75,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f70,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (2349)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (2337)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (2337)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f79,f83,f87,f99,f103,f108,f112,f122,f126,f156,f171,f186,f234])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ~spl2_5 | ~spl2_7 | ~spl2_21 | ~spl2_24),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    $false | (~spl2_5 | ~spl2_7 | ~spl2_21 | ~spl2_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f232,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl2_5 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    sK1 != k5_xboole_0(sK1,k1_xboole_0) | (~spl2_7 | ~spl2_21 | ~spl2_24)),
% 0.21/0.46    inference(forward_demodulation,[],[f230,f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | ~spl2_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl2_7 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.46  fof(f230,plain,(
% 0.21/0.46    sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))) | (~spl2_21 | ~spl2_24)),
% 0.21/0.46    inference(superposition,[],[f185,f170])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl2_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f168])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    spl2_21 <=> k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X0))) != X0) ) | ~spl2_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f184])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    spl2_24 <=> ! [X0] : k5_xboole_0(X0,k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X0))) != X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    spl2_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f50,f184])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X0))) != X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f34,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0] : (k1_ordinal1(X0) = k5_xboole_0(X0,k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X0)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f39,f48,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f45,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : k1_ordinal1(X0) != X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    spl2_21 | spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f166,f153,f106,f67,f57,f168])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl2_1 <=> v1_xboole_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl2_12 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    spl2_19 <=> k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    k1_xboole_0 = k2_tarski(sK1,sK1) | (spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_19)),
% 0.21/0.46    inference(forward_demodulation,[],[f165,f155])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    k1_xboole_0 = k6_domain_1(sK0,sK1) | ~spl2_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f153])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | (spl2_1 | ~spl2_3 | ~spl2_12)),
% 0.21/0.46    inference(subsumption_resolution,[],[f162,f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ~v1_xboole_0(sK0) | spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f57])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(sK0) | (~spl2_3 | ~spl2_12)),
% 0.21/0.46    inference(resolution,[],[f107,f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f67])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) ) | ~spl2_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f106])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    spl2_19 | ~spl2_6 | ~spl2_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f128,f115,f81,f153])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl2_6 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl2_14 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    k1_xboole_0 = k6_domain_1(sK0,sK1) | (~spl2_6 | ~spl2_14)),
% 0.21/0.46    inference(resolution,[],[f117,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  % (2336)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl2_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f115])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    spl2_1 | ~spl2_3 | ~spl2_10 | spl2_15),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    $false | (spl2_1 | ~spl2_3 | ~spl2_10 | spl2_15)),
% 0.21/0.46    inference(subsumption_resolution,[],[f124,f59])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    v1_xboole_0(sK0) | (~spl2_3 | ~spl2_10 | spl2_15)),
% 0.21/0.46    inference(subsumption_resolution,[],[f123,f69])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_10 | spl2_15)),
% 0.21/0.46    inference(resolution,[],[f121,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl2_10 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl2_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f119])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    spl2_15 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    spl2_14 | ~spl2_15 | ~spl2_4 | ~spl2_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f113,f110,f72,f119,f115])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl2_13 <=> ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_subset_1(X0,sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k6_domain_1(sK0,sK1)) | (~spl2_4 | ~spl2_13)),
% 0.21/0.46    inference(resolution,[],[f111,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f72])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0)) ) | ~spl2_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f110])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    spl2_13 | ~spl2_2 | ~spl2_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f104,f101,f62,f110])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl2_11 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_subset_1(X0,sK0)) ) | (~spl2_2 | ~spl2_11)),
% 0.21/0.46    inference(resolution,[],[f102,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f62])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) ) | ~spl2_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f101])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    spl2_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f54,f106])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f46,f38])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl2_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f55,f101])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f42,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl2_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f47,f97])).
% 0.21/0.46  % (2335)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl2_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f51,f85])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f35,f44])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl2_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f40,f81])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl2_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f77])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f72])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f28,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.46    inference(negated_conjecture,[],[f15])).
% 0.21/0.46  fof(f15,conjecture,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f67])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    m1_subset_1(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f62])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v1_zfmisc_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ~spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f57])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ~v1_xboole_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (2337)------------------------------
% 0.21/0.46  % (2337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2337)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (2337)Memory used [KB]: 6140
% 0.21/0.46  % (2337)Time elapsed: 0.009 s
% 0.21/0.46  % (2337)------------------------------
% 0.21/0.46  % (2337)------------------------------
% 0.21/0.46  % (2329)Success in time 0.106 s
%------------------------------------------------------------------------------
