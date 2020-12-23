%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 213 expanded)
%              Number of leaves         :   39 ( 103 expanded)
%              Depth                    :    7
%              Number of atoms          :  349 ( 603 expanded)
%              Number of equality atoms :   48 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f433,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f85,f89,f97,f101,f109,f117,f131,f135,f139,f151,f157,f172,f193,f199,f234,f310,f324,f357,f425,f432])).

fof(f432,plain,
    ( ~ spl2_9
    | ~ spl2_46
    | ~ spl2_52 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl2_9
    | ~ spl2_46
    | ~ spl2_52 ),
    inference(subsumption_resolution,[],[f356,f427])).

fof(f427,plain,
    ( ! [X1] : k1_xboole_0 != k1_tarski(X1)
    | ~ spl2_9
    | ~ spl2_52 ),
    inference(superposition,[],[f96,f424])).

fof(f424,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl2_52
  <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f96,plain,
    ( ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_9
  <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f356,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl2_46
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f425,plain,
    ( spl2_52
    | ~ spl2_7
    | ~ spl2_16
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f328,f322,f129,f87,f423])).

fof(f87,plain,
    ( spl2_7
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f129,plain,
    ( spl2_16
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f322,plain,
    ( spl2_42
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f328,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_7
    | ~ spl2_16
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f327,f88])).

fof(f88,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f327,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)
    | ~ spl2_16
    | ~ spl2_42 ),
    inference(superposition,[],[f130,f323])).

fof(f323,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f322])).

fof(f130,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f357,plain,
    ( spl2_46
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f316,f300,f107,f78,f354])).

fof(f78,plain,
    ( spl2_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f107,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f300,plain,
    ( spl2_40
  <=> v1_xboole_0(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f316,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_40 ),
    inference(unit_resulting_resolution,[],[f80,f302,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f302,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f300])).

fof(f80,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f324,plain,
    ( spl2_42
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f245,f232,f133,f87,f322])).

fof(f133,plain,
    ( spl2_17
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f232,plain,
    ( spl2_32
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f245,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f240,f88])).

fof(f240,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f134,f233])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f232])).

fof(f134,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f310,plain,
    ( spl2_40
    | spl2_1
    | ~ spl2_2
    | ~ spl2_22
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f214,f190,f185,f170,f63,f58,f300])).

fof(f58,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f170,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f185,plain,
    ( spl2_24
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f190,plain,
    ( spl2_25
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f214,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_22
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f60,f65,f192,f187,f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f187,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f185])).

fof(f192,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f190])).

fof(f65,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f60,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f234,plain,
    ( spl2_32
    | ~ spl2_14
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f147,f137,f115,f232])).

fof(f115,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f137,plain,
    ( spl2_18
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_14
    | ~ spl2_18 ),
    inference(superposition,[],[f138,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f138,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f199,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_24
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f161,f149,f73,f185,f68,f58])).

fof(f68,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f73,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f149,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f161,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(superposition,[],[f75,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f75,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f193,plain,
    ( spl2_25
    | spl2_1
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f168,f155,f149,f68,f58,f190])).

fof(f155,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f168,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f162,f160])).

fof(f160,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f60,f70,f150])).

fof(f70,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f162,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f60,f70,f156])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f172,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f45,f170])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f157,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f52,f155])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f151,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f51,f149])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f139,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f49,f137])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f135,plain,
    ( spl2_17
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f118,f99,f83,f133])).

fof(f83,plain,
    ( spl2_6
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f99,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f118,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f84,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f84,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f131,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f48,f129])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f117,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f50,f115])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f109,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f55,f107])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f101,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f53,f99])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f46,f95])).

fof(f46,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f89,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f85,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f41,f83])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f81,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f76,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f33,f32])).

fof(f32,plain,
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

fof(f33,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f71,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f37,f68])).

fof(f37,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f39,f63])).

fof(f39,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f36,f58])).

fof(f36,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (30633)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.44  % (30630)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (30630)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f433,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f85,f89,f97,f101,f109,f117,f131,f135,f139,f151,f157,f172,f193,f199,f234,f310,f324,f357,f425,f432])).
% 0.20/0.45  fof(f432,plain,(
% 0.20/0.45    ~spl2_9 | ~spl2_46 | ~spl2_52),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f431])).
% 0.20/0.45  fof(f431,plain,(
% 0.20/0.45    $false | (~spl2_9 | ~spl2_46 | ~spl2_52)),
% 0.20/0.45    inference(subsumption_resolution,[],[f356,f427])).
% 0.20/0.45  fof(f427,plain,(
% 0.20/0.45    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) ) | (~spl2_9 | ~spl2_52)),
% 0.20/0.45    inference(superposition,[],[f96,f424])).
% 0.20/0.45  fof(f424,plain,(
% 0.20/0.45    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl2_52),
% 0.20/0.45    inference(avatar_component_clause,[],[f423])).
% 0.20/0.45  fof(f423,plain,(
% 0.20/0.45    spl2_52 <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) ) | ~spl2_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f95])).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    spl2_9 <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.45  fof(f356,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tarski(sK1) | ~spl2_46),
% 0.20/0.45    inference(avatar_component_clause,[],[f354])).
% 0.20/0.45  fof(f354,plain,(
% 0.20/0.45    spl2_46 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.20/0.45  fof(f425,plain,(
% 0.20/0.45    spl2_52 | ~spl2_7 | ~spl2_16 | ~spl2_42),
% 0.20/0.45    inference(avatar_split_clause,[],[f328,f322,f129,f87,f423])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    spl2_7 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.45  fof(f129,plain,(
% 0.20/0.45    spl2_16 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.45  fof(f322,plain,(
% 0.20/0.45    spl2_42 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.20/0.45  fof(f328,plain,(
% 0.20/0.45    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl2_7 | ~spl2_16 | ~spl2_42)),
% 0.20/0.45    inference(forward_demodulation,[],[f327,f88])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f87])).
% 0.20/0.45  fof(f327,plain,(
% 0.20/0.45    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) ) | (~spl2_16 | ~spl2_42)),
% 0.20/0.45    inference(superposition,[],[f130,f323])).
% 0.20/0.45  fof(f323,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_42),
% 0.20/0.45    inference(avatar_component_clause,[],[f322])).
% 0.20/0.45  fof(f130,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f129])).
% 0.20/0.45  fof(f357,plain,(
% 0.20/0.45    spl2_46 | ~spl2_5 | ~spl2_12 | ~spl2_40),
% 0.20/0.45    inference(avatar_split_clause,[],[f316,f300,f107,f78,f354])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    spl2_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    spl2_12 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.45  fof(f300,plain,(
% 0.20/0.45    spl2_40 <=> v1_xboole_0(k1_tarski(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.20/0.45  fof(f316,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tarski(sK1) | (~spl2_5 | ~spl2_12 | ~spl2_40)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f80,f302,f108])).
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) ) | ~spl2_12),
% 0.20/0.45    inference(avatar_component_clause,[],[f107])).
% 0.20/0.45  fof(f302,plain,(
% 0.20/0.45    v1_xboole_0(k1_tarski(sK1)) | ~spl2_40),
% 0.20/0.45    inference(avatar_component_clause,[],[f300])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0) | ~spl2_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f78])).
% 0.20/0.45  fof(f324,plain,(
% 0.20/0.45    spl2_42 | ~spl2_7 | ~spl2_17 | ~spl2_32),
% 0.20/0.45    inference(avatar_split_clause,[],[f245,f232,f133,f87,f322])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    spl2_17 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.45  fof(f232,plain,(
% 0.20/0.45    spl2_32 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.20/0.45  fof(f245,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_7 | ~spl2_17 | ~spl2_32)),
% 0.20/0.45    inference(forward_demodulation,[],[f240,f88])).
% 0.20/0.45  fof(f240,plain,(
% 0.20/0.45    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) | (~spl2_17 | ~spl2_32)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f134,f233])).
% 0.20/0.45  fof(f233,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) ) | ~spl2_32),
% 0.20/0.45    inference(avatar_component_clause,[],[f232])).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_17),
% 0.20/0.45    inference(avatar_component_clause,[],[f133])).
% 0.20/0.45  fof(f310,plain,(
% 0.20/0.45    spl2_40 | spl2_1 | ~spl2_2 | ~spl2_22 | ~spl2_24 | ~spl2_25),
% 0.20/0.45    inference(avatar_split_clause,[],[f214,f190,f185,f170,f63,f58,f300])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    spl2_1 <=> v1_xboole_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.45  fof(f170,plain,(
% 0.20/0.45    spl2_22 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.45  fof(f185,plain,(
% 0.20/0.45    spl2_24 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.45  fof(f190,plain,(
% 0.20/0.45    spl2_25 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.45  fof(f214,plain,(
% 0.20/0.45    v1_xboole_0(k1_tarski(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_22 | ~spl2_24 | ~spl2_25)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f60,f65,f192,f187,f171])).
% 0.20/0.45  fof(f171,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_22),
% 0.20/0.45    inference(avatar_component_clause,[],[f170])).
% 0.20/0.45  fof(f187,plain,(
% 0.20/0.45    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_24),
% 0.20/0.45    inference(avatar_component_clause,[],[f185])).
% 0.20/0.45  fof(f192,plain,(
% 0.20/0.45    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_25),
% 0.20/0.45    inference(avatar_component_clause,[],[f190])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f63])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ~v1_xboole_0(sK0) | spl2_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f58])).
% 0.20/0.45  fof(f234,plain,(
% 0.20/0.45    spl2_32 | ~spl2_14 | ~spl2_18),
% 0.20/0.45    inference(avatar_split_clause,[],[f147,f137,f115,f232])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    spl2_14 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    spl2_18 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.45  fof(f147,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) ) | (~spl2_14 | ~spl2_18)),
% 0.20/0.45    inference(superposition,[],[f138,f116])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f115])).
% 0.20/0.45  fof(f138,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_18),
% 0.20/0.45    inference(avatar_component_clause,[],[f137])).
% 0.20/0.45  fof(f199,plain,(
% 0.20/0.45    spl2_1 | ~spl2_3 | spl2_24 | ~spl2_4 | ~spl2_20),
% 0.20/0.45    inference(avatar_split_clause,[],[f161,f149,f73,f185,f68,f58])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.45  fof(f149,plain,(
% 0.20/0.45    spl2_20 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.45  fof(f161,plain,(
% 0.20/0.45    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_4 | ~spl2_20)),
% 0.20/0.45    inference(superposition,[],[f75,f150])).
% 0.20/0.45  fof(f150,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_20),
% 0.20/0.45    inference(avatar_component_clause,[],[f149])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f73])).
% 0.20/0.45  fof(f193,plain,(
% 0.20/0.45    spl2_25 | spl2_1 | ~spl2_3 | ~spl2_20 | ~spl2_21),
% 0.20/0.45    inference(avatar_split_clause,[],[f168,f155,f149,f68,f58,f190])).
% 0.20/0.45  fof(f155,plain,(
% 0.20/0.45    spl2_21 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.45  fof(f168,plain,(
% 0.20/0.45    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_20 | ~spl2_21)),
% 0.20/0.45    inference(forward_demodulation,[],[f162,f160])).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | (spl2_1 | ~spl2_3 | ~spl2_20)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f60,f70,f150])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f68])).
% 0.20/0.45  fof(f162,plain,(
% 0.20/0.45    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_21)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f60,f70,f156])).
% 0.20/0.45  fof(f156,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_21),
% 0.20/0.45    inference(avatar_component_clause,[],[f155])).
% 0.20/0.45  fof(f172,plain,(
% 0.20/0.45    spl2_22),
% 0.20/0.45    inference(avatar_split_clause,[],[f45,f170])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,axiom,(
% 0.20/0.45    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.45  fof(f157,plain,(
% 0.20/0.45    spl2_21),
% 0.20/0.45    inference(avatar_split_clause,[],[f52,f155])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.45  fof(f151,plain,(
% 0.20/0.45    spl2_20),
% 0.20/0.45    inference(avatar_split_clause,[],[f51,f149])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.45  fof(f139,plain,(
% 0.20/0.45    spl2_18),
% 0.20/0.45    inference(avatar_split_clause,[],[f49,f137])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    spl2_17 | ~spl2_6 | ~spl2_10),
% 0.20/0.45    inference(avatar_split_clause,[],[f118,f99,f83,f133])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    spl2_6 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    spl2_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl2_6 | ~spl2_10)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f84,f100])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f99])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f83])).
% 0.20/0.45  fof(f131,plain,(
% 0.20/0.45    spl2_16),
% 0.20/0.45    inference(avatar_split_clause,[],[f48,f129])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    spl2_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f50,f115])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    spl2_12),
% 0.20/0.45    inference(avatar_split_clause,[],[f55,f107])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    spl2_10),
% 0.20/0.45    inference(avatar_split_clause,[],[f53,f99])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.45    inference(nnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    spl2_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f46,f95])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    spl2_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f42,f87])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    spl2_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f41,f83])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    spl2_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f40,f78])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    spl2_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f38,f73])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f33,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.45    inference(negated_conjecture,[],[f17])).
% 0.20/0.45  fof(f17,conjecture,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    spl2_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f37,f68])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    m1_subset_1(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    spl2_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f39,f63])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    v1_zfmisc_1(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ~spl2_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f36,f58])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ~v1_xboole_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (30630)------------------------------
% 0.20/0.45  % (30630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (30630)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (30630)Memory used [KB]: 6268
% 0.20/0.45  % (30630)Time elapsed: 0.018 s
% 0.20/0.45  % (30630)------------------------------
% 0.20/0.45  % (30630)------------------------------
% 0.20/0.45  % (30624)Success in time 0.096 s
%------------------------------------------------------------------------------
