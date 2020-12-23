%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:48 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 153 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  279 ( 440 expanded)
%              Number of equality atoms :  108 ( 190 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f57,f61,f69,f73,f77,f81,f93,f97,f101,f110,f115,f120,f132,f148,f152])).

fof(f152,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f150,f118,f75,f52,f48,f130])).

fof(f130,plain,
    ( spl3_22
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f48,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( spl3_4
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X2] : k4_tarski(X1,X2) != X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f118,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
        | k1_xboole_0 = k2_zfmisc_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f150,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f149,f76])).

fof(f76,plain,
    ( ! [X2,X1] : k4_tarski(X1,X2) != X2
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f149,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f121,f53])).

fof(f53,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f121,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(resolution,[],[f119,f49])).

fof(f49,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | k1_xboole_0 = k2_zfmisc_1(X1,X2) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f118])).

fof(f148,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f146,f41])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f146,plain,
    ( k1_xboole_0 = sK0
    | spl3_1
    | spl3_2
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f145,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f145,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | spl3_1
    | spl3_2
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f144,f41])).

fof(f144,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f137,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(superposition,[],[f100,f131])).

fof(f131,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f130])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f132,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f123,f118,f79,f55,f48,f130])).

fof(f55,plain,
    ( spl3_5
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X2] : k4_tarski(X1,X2) != X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f123,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f122,f80])).

fof(f80,plain,
    ( ! [X2,X1] : k4_tarski(X1,X2) != X1
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f122,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f121,f56])).

fof(f56,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f120,plain,
    ( spl3_20
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f116,f113,f71,f118])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f113,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | v1_xboole_0(k2_zfmisc_1(X1,X2))
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
        | k1_xboole_0 = k2_zfmisc_1(X1,X2) )
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(resolution,[],[f114,f72])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X1,X2))
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl3_19
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f111,f108,f91,f113])).

fof(f91,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f108,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | v1_xboole_0(k2_zfmisc_1(X1,X2))
        | ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2)) )
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(resolution,[],[f109,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl3_18
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f106,f95,f67,f108])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f95,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,X1)
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 )
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(resolution,[],[f96,f68])).

fof(f68,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,X1)
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f101,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f33,f99])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f97,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f31,f95])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f93,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f32,f91])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f81,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X1 ),
    inference(backward_demodulation,[],[f36,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f36,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k1_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f37,f75])).

fof(f37,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k2_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f25,f71])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f57,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f19,f55,f52])).

fof(f19,plain,
    ( sK2 = k1_mcart_1(sK2)
    | sK2 = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f50,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:18:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (22685)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (22693)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (22685)Refutation not found, incomplete strategy% (22685)------------------------------
% 0.20/0.49  % (22685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22685)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (22685)Memory used [KB]: 6012
% 0.20/0.49  % (22685)Time elapsed: 0.003 s
% 0.20/0.49  % (22685)------------------------------
% 0.20/0.49  % (22685)------------------------------
% 0.20/0.49  % (22693)Refutation not found, incomplete strategy% (22693)------------------------------
% 0.20/0.49  % (22693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (22693)Memory used [KB]: 10618
% 0.20/0.49  % (22693)Time elapsed: 0.066 s
% 0.20/0.49  % (22693)------------------------------
% 0.20/0.49  % (22693)------------------------------
% 0.20/0.50  % (22674)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (22673)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (22674)Refutation not found, incomplete strategy% (22674)------------------------------
% 0.20/0.50  % (22674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22674)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (22674)Memory used [KB]: 10618
% 0.20/0.50  % (22674)Time elapsed: 0.063 s
% 0.20/0.50  % (22674)------------------------------
% 0.20/0.50  % (22674)------------------------------
% 0.20/0.51  % (22686)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (22686)Refutation not found, incomplete strategy% (22686)------------------------------
% 0.20/0.51  % (22686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22686)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (22686)Memory used [KB]: 1535
% 0.20/0.51  % (22686)Time elapsed: 0.082 s
% 0.20/0.51  % (22686)------------------------------
% 0.20/0.51  % (22686)------------------------------
% 0.20/0.51  % (22676)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (22680)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (22684)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (22687)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.52  % (22678)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (22688)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.52  % (22682)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (22681)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (22688)Refutation not found, incomplete strategy% (22688)------------------------------
% 0.20/0.52  % (22688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22688)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22688)Memory used [KB]: 6140
% 0.20/0.52  % (22688)Time elapsed: 0.070 s
% 0.20/0.52  % (22688)------------------------------
% 0.20/0.52  % (22688)------------------------------
% 0.20/0.53  % (22675)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.34/0.53  % (22682)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f153,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f42,f46,f50,f57,f61,f69,f73,f77,f81,f93,f97,f101,f110,f115,f120,f132,f148,f152])).
% 1.34/0.53  fof(f152,plain,(
% 1.34/0.53    spl3_22 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_20),
% 1.34/0.53    inference(avatar_split_clause,[],[f150,f118,f75,f52,f48,f130])).
% 1.34/0.53  fof(f130,plain,(
% 1.34/0.53    spl3_22 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    spl3_4 <=> sK2 = k2_mcart_1(sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.34/0.53  fof(f75,plain,(
% 1.34/0.53    spl3_10 <=> ! [X1,X2] : k4_tarski(X1,X2) != X2),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.34/0.53  fof(f118,plain,(
% 1.34/0.53    spl3_20 <=> ! [X1,X0,X2] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | k1_xboole_0 = k2_zfmisc_1(X1,X2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.34/0.53  fof(f150,plain,(
% 1.34/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_20)),
% 1.34/0.53    inference(subsumption_resolution,[],[f149,f76])).
% 1.34/0.53  fof(f76,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) ) | ~spl3_10),
% 1.34/0.53    inference(avatar_component_clause,[],[f75])).
% 1.34/0.53  fof(f149,plain,(
% 1.34/0.53    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_20)),
% 1.34/0.53    inference(backward_demodulation,[],[f121,f53])).
% 1.34/0.53  fof(f53,plain,(
% 1.34/0.53    sK2 = k2_mcart_1(sK2) | ~spl3_4),
% 1.34/0.53    inference(avatar_component_clause,[],[f52])).
% 1.34/0.53  fof(f121,plain,(
% 1.34/0.53    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_3 | ~spl3_20)),
% 1.34/0.53    inference(resolution,[],[f119,f49])).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 1.34/0.53    inference(avatar_component_clause,[],[f48])).
% 1.34/0.53  fof(f119,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | k1_xboole_0 = k2_zfmisc_1(X1,X2)) ) | ~spl3_20),
% 1.34/0.53    inference(avatar_component_clause,[],[f118])).
% 1.34/0.53  fof(f148,plain,(
% 1.34/0.53    spl3_1 | spl3_2 | ~spl3_6 | ~spl3_16 | ~spl3_22),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f147])).
% 1.34/0.53  fof(f147,plain,(
% 1.34/0.53    $false | (spl3_1 | spl3_2 | ~spl3_6 | ~spl3_16 | ~spl3_22)),
% 1.34/0.53    inference(subsumption_resolution,[],[f146,f41])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    k1_xboole_0 != sK0 | spl3_1),
% 1.34/0.53    inference(avatar_component_clause,[],[f40])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    spl3_1 <=> k1_xboole_0 = sK0),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.34/0.53  fof(f146,plain,(
% 1.34/0.53    k1_xboole_0 = sK0 | (spl3_1 | spl3_2 | ~spl3_6 | ~spl3_16 | ~spl3_22)),
% 1.34/0.53    inference(forward_demodulation,[],[f145,f60])).
% 1.34/0.53  fof(f60,plain,(
% 1.34/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f59])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    spl3_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.34/0.53  fof(f145,plain,(
% 1.34/0.53    k1_relat_1(k1_xboole_0) = sK0 | (spl3_1 | spl3_2 | ~spl3_16 | ~spl3_22)),
% 1.34/0.53    inference(subsumption_resolution,[],[f144,f41])).
% 1.34/0.53  fof(f144,plain,(
% 1.34/0.53    k1_relat_1(k1_xboole_0) = sK0 | k1_xboole_0 = sK0 | (spl3_2 | ~spl3_16 | ~spl3_22)),
% 1.34/0.53    inference(subsumption_resolution,[],[f137,f45])).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    k1_xboole_0 != sK1 | spl3_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f44])).
% 1.34/0.53  fof(f44,plain,(
% 1.34/0.53    spl3_2 <=> k1_xboole_0 = sK1),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.34/0.53  fof(f137,plain,(
% 1.34/0.53    k1_relat_1(k1_xboole_0) = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl3_16 | ~spl3_22)),
% 1.34/0.53    inference(superposition,[],[f100,f131])).
% 1.34/0.53  fof(f131,plain,(
% 1.34/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_22),
% 1.34/0.53    inference(avatar_component_clause,[],[f130])).
% 1.34/0.53  fof(f100,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl3_16),
% 1.34/0.53    inference(avatar_component_clause,[],[f99])).
% 1.34/0.53  fof(f99,plain,(
% 1.34/0.53    spl3_16 <=> ! [X1,X0] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.34/0.53  fof(f132,plain,(
% 1.34/0.53    spl3_22 | ~spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_20),
% 1.34/0.53    inference(avatar_split_clause,[],[f123,f118,f79,f55,f48,f130])).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    spl3_5 <=> sK2 = k1_mcart_1(sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.34/0.53  fof(f79,plain,(
% 1.34/0.53    spl3_11 <=> ! [X1,X2] : k4_tarski(X1,X2) != X1),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.34/0.53  fof(f123,plain,(
% 1.34/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_20)),
% 1.34/0.53    inference(subsumption_resolution,[],[f122,f80])).
% 1.34/0.53  fof(f80,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k4_tarski(X1,X2) != X1) ) | ~spl3_11),
% 1.34/0.53    inference(avatar_component_clause,[],[f79])).
% 1.34/0.53  fof(f122,plain,(
% 1.34/0.53    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_3 | ~spl3_5 | ~spl3_20)),
% 1.34/0.53    inference(forward_demodulation,[],[f121,f56])).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    sK2 = k1_mcart_1(sK2) | ~spl3_5),
% 1.34/0.53    inference(avatar_component_clause,[],[f55])).
% 1.34/0.53  fof(f120,plain,(
% 1.34/0.53    spl3_20 | ~spl3_9 | ~spl3_19),
% 1.34/0.53    inference(avatar_split_clause,[],[f116,f113,f71,f118])).
% 1.34/0.53  fof(f71,plain,(
% 1.34/0.53    spl3_9 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.34/0.53  fof(f113,plain,(
% 1.34/0.53    spl3_19 <=> ! [X1,X0,X2] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | v1_xboole_0(k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.34/0.53  fof(f116,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | k1_xboole_0 = k2_zfmisc_1(X1,X2)) ) | (~spl3_9 | ~spl3_19)),
% 1.34/0.53    inference(resolution,[],[f114,f72])).
% 1.34/0.53  fof(f72,plain,(
% 1.34/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_9),
% 1.34/0.53    inference(avatar_component_clause,[],[f71])).
% 1.34/0.53  fof(f114,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (v1_xboole_0(k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2))) ) | ~spl3_19),
% 1.34/0.53    inference(avatar_component_clause,[],[f113])).
% 1.34/0.53  fof(f115,plain,(
% 1.34/0.53    spl3_19 | ~spl3_14 | ~spl3_18),
% 1.34/0.53    inference(avatar_split_clause,[],[f111,f108,f91,f113])).
% 1.34/0.53  fof(f91,plain,(
% 1.34/0.53    spl3_14 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.34/0.53  fof(f108,plain,(
% 1.34/0.53    spl3_18 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.34/0.53  fof(f111,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | v1_xboole_0(k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X0,k2_zfmisc_1(X1,X2))) ) | (~spl3_14 | ~spl3_18)),
% 1.34/0.53    inference(resolution,[],[f109,f92])).
% 1.34/0.53  fof(f92,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl3_14),
% 1.34/0.53    inference(avatar_component_clause,[],[f91])).
% 1.34/0.53  fof(f109,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) ) | ~spl3_18),
% 1.34/0.53    inference(avatar_component_clause,[],[f108])).
% 1.34/0.53  fof(f110,plain,(
% 1.34/0.53    spl3_18 | ~spl3_8 | ~spl3_15),
% 1.34/0.53    inference(avatar_split_clause,[],[f106,f95,f67,f108])).
% 1.34/0.53  fof(f67,plain,(
% 1.34/0.53    spl3_8 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.34/0.53  fof(f95,plain,(
% 1.34/0.53    spl3_15 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.34/0.53  fof(f106,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) ) | (~spl3_8 | ~spl3_15)),
% 1.34/0.53    inference(resolution,[],[f96,f68])).
% 1.34/0.53  fof(f68,plain,(
% 1.34/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_8),
% 1.34/0.53    inference(avatar_component_clause,[],[f67])).
% 1.34/0.53  fof(f96,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) ) | ~spl3_15),
% 1.34/0.53    inference(avatar_component_clause,[],[f95])).
% 1.34/0.53  fof(f101,plain,(
% 1.34/0.53    spl3_16),
% 1.34/0.53    inference(avatar_split_clause,[],[f33,f99])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.34/0.53    inference(ennf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 1.34/0.53  fof(f97,plain,(
% 1.34/0.53    spl3_15),
% 1.34/0.53    inference(avatar_split_clause,[],[f31,f95])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(flattening,[],[f14])).
% 1.34/0.53  fof(f14,plain,(
% 1.34/0.53    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.34/0.53  fof(f93,plain,(
% 1.34/0.53    spl3_14),
% 1.34/0.53    inference(avatar_split_clause,[],[f32,f91])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f17])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.34/0.53    inference(flattening,[],[f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.34/0.53  fof(f81,plain,(
% 1.34/0.53    spl3_11),
% 1.34/0.53    inference(avatar_split_clause,[],[f38,f79])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k4_tarski(X1,X2) != X1) )),
% 1.34/0.53    inference(backward_demodulation,[],[f36,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,axiom,(
% 1.34/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 1.34/0.53    inference(equality_resolution,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k1_mcart_1(X0) != X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.34/0.53    inference(ennf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.34/0.53  fof(f77,plain,(
% 1.34/0.53    spl3_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f37,f75])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.34/0.53    inference(backward_demodulation,[],[f35,f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f8])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.34/0.53    inference(equality_resolution,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k2_mcart_1(X0) != X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  fof(f73,plain,(
% 1.34/0.53    spl3_9),
% 1.34/0.53    inference(avatar_split_clause,[],[f25,f71])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,plain,(
% 1.34/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.34/0.53    inference(ennf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.34/0.53  fof(f69,plain,(
% 1.34/0.53    spl3_8),
% 1.34/0.53    inference(avatar_split_clause,[],[f28,f67])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.53  fof(f61,plain,(
% 1.34/0.53    spl3_6),
% 1.34/0.53    inference(avatar_split_clause,[],[f23,f59])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    spl3_4 | spl3_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f19,f55,f52])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    sK2 = k1_mcart_1(sK2) | sK2 = k2_mcart_1(sK2)),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,plain,(
% 1.34/0.53    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.34/0.53    inference(ennf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.34/0.53    inference(negated_conjecture,[],[f9])).
% 1.34/0.53  fof(f9,conjecture,(
% 1.34/0.53    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    spl3_3),
% 1.34/0.53    inference(avatar_split_clause,[],[f20,f48])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    ~spl3_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f22,f44])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    k1_xboole_0 != sK1),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ~spl3_1),
% 1.34/0.53    inference(avatar_split_clause,[],[f21,f40])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    k1_xboole_0 != sK0),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (22682)------------------------------
% 1.34/0.53  % (22682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (22682)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (22682)Memory used [KB]: 10618
% 1.34/0.53  % (22682)Time elapsed: 0.095 s
% 1.34/0.53  % (22682)------------------------------
% 1.34/0.53  % (22682)------------------------------
% 1.34/0.53  % (22672)Success in time 0.167 s
%------------------------------------------------------------------------------
