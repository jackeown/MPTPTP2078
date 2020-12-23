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
% DateTime   : Thu Dec  3 12:47:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 150 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  277 ( 406 expanded)
%              Number of equality atoms :   54 (  77 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f49,f53,f57,f61,f65,f79,f83,f87,f91,f104,f120,f126,f132,f147,f164,f237,f250,f267])).

fof(f267,plain,
    ( ~ spl5_2
    | spl5_3
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_35 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl5_2
    | spl5_3
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f265,f48])).

fof(f48,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f265,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_35 ),
    inference(forward_demodulation,[],[f264,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f264,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f258,f78])).

fof(f78,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_10
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f258,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_35 ),
    inference(superposition,[],[f90,f249])).

fof(f249,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl5_35
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f90,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_13
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f250,plain,
    ( spl5_35
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f242,f235,f77,f44,f40,f248])).

fof(f40,plain,
    ( spl5_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f235,plain,
    ( spl5_33
  <=> ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f242,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f241,f41])).

fof(f41,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f241,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f240,f174])).

fof(f240,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl5_10
    | ~ spl5_33 ),
    inference(resolution,[],[f236,f78])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_xboole_0(k2_relat_1(X0)) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f235])).

fof(f237,plain,
    ( spl5_33
    | ~ spl5_5
    | ~ spl5_13
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f185,f124,f89,f55,f235])).

fof(f55,plain,
    ( spl5_5
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k4_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f124,plain,
    ( spl5_20
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_5
    | ~ spl5_13
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f184,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | ~ v1_relat_1(k4_relat_1(X0))
        | k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_13
    | ~ spl5_20 ),
    inference(superposition,[],[f125,f90])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f124])).

fof(f164,plain,
    ( spl5_2
    | ~ spl5_12
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl5_2
    | ~ spl5_12
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f157,f45])).

fof(f45,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f157,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_24 ),
    inference(resolution,[],[f146,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_12
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f146,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_24
  <=> ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f147,plain,
    ( spl5_24
    | ~ spl5_1
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f137,f130,f40,f145])).

fof(f130,plain,
    ( spl5_21
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k2_relat_1(X3))
        | ~ v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f137,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl5_1
    | ~ spl5_21 ),
    inference(resolution,[],[f131,f41])).

fof(f131,plain,
    ( ! [X2,X3] :
        ( ~ v1_xboole_0(X3)
        | ~ r2_hidden(X2,k2_relat_1(X3)) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl5_21
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f128,f118,f59,f130])).

fof(f59,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f118,plain,
    ( spl5_19
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f128,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k2_relat_1(X3))
        | ~ v1_xboole_0(X3) )
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(resolution,[],[f119,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f119,plain,
    ( ! [X2,X0] :
        ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f126,plain,
    ( spl5_20
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f106,f102,f81,f124])).

fof(f81,plain,
    ( spl5_11
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f102,plain,
    ( spl5_16
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f106,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k1_relat_1(X0)) )
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(resolution,[],[f103,f82])).

fof(f82,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k1_relat_1(X0)) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f102])).

fof(f120,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f35,f118])).

fof(f35,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f104,plain,
    ( spl5_16
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f96,f85,f59,f102])).

fof(f96,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f86,f60])).

fof(f91,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f21,f89])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f87,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f26,f85])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f83,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f23,f81])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f79,plain,
    ( spl5_10
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f74,f63,f51,f77])).

fof(f51,plain,
    ( spl5_4
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f63,plain,
    ( spl5_7
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f74,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(superposition,[],[f52,f64])).

fof(f64,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f52,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f65,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f37,f63])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
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

fof(f61,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f53,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f49,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f18,f47,f44])).

fof(f18,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f42,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (17083)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.45  % (17088)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (17088)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f268,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f42,f49,f53,f57,f61,f65,f79,f83,f87,f91,f104,f120,f126,f132,f147,f164,f237,f250,f267])).
% 0.20/0.47  fof(f267,plain,(
% 0.20/0.47    ~spl5_2 | spl5_3 | ~spl5_10 | ~spl5_13 | ~spl5_35),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.47  fof(f266,plain,(
% 0.20/0.47    $false | (~spl5_2 | spl5_3 | ~spl5_10 | ~spl5_13 | ~spl5_35)),
% 0.20/0.47    inference(subsumption_resolution,[],[f265,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl5_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f265,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_2 | ~spl5_10 | ~spl5_13 | ~spl5_35)),
% 0.20/0.47    inference(forward_demodulation,[],[f264,f174])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl5_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f264,plain,(
% 0.20/0.47    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) | (~spl5_10 | ~spl5_13 | ~spl5_35)),
% 0.20/0.47    inference(subsumption_resolution,[],[f258,f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    v1_relat_1(k1_xboole_0) | ~spl5_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl5_10 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.47  fof(f258,plain,(
% 0.20/0.47    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl5_13 | ~spl5_35)),
% 0.20/0.47    inference(superposition,[],[f90,f249])).
% 0.20/0.47  fof(f249,plain,(
% 0.20/0.47    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl5_35),
% 0.20/0.47    inference(avatar_component_clause,[],[f248])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    spl5_35 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl5_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl5_13 <=> ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    spl5_35 | ~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_33),
% 0.20/0.47    inference(avatar_split_clause,[],[f242,f235,f77,f44,f40,f248])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl5_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f235,plain,(
% 0.20/0.47    spl5_33 <=> ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | k1_xboole_0 = k4_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_33)),
% 0.20/0.47    inference(subsumption_resolution,[],[f241,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f40])).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl5_2 | ~spl5_10 | ~spl5_33)),
% 0.20/0.47    inference(forward_demodulation,[],[f240,f174])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(k1_xboole_0)) | (~spl5_10 | ~spl5_33)),
% 0.20/0.47    inference(resolution,[],[f236,f78])).
% 0.20/0.47  fof(f236,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k4_relat_1(X0) | ~v1_xboole_0(k2_relat_1(X0))) ) | ~spl5_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f235])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    spl5_33 | ~spl5_5 | ~spl5_13 | ~spl5_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f185,f124,f89,f55,f235])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl5_5 <=> ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl5_20 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(X0) | ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | k1_xboole_0 = k4_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl5_5 | ~spl5_13 | ~spl5_20)),
% 0.20/0.47    inference(subsumption_resolution,[],[f184,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl5_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | k1_xboole_0 = k4_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl5_13 | ~spl5_20)),
% 0.20/0.47    inference(superposition,[],[f125,f90])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl5_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl5_2 | ~spl5_12 | ~spl5_24),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    $false | (spl5_2 | ~spl5_12 | ~spl5_24)),
% 0.20/0.47    inference(subsumption_resolution,[],[f157,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f44])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl5_12 | ~spl5_24)),
% 0.20/0.47    inference(resolution,[],[f146,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl5_12 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | ~spl5_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f145])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    spl5_24 <=> ! [X0] : ~r2_hidden(X0,k2_relat_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    spl5_24 | ~spl5_1 | ~spl5_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f137,f130,f40,f145])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    spl5_21 <=> ! [X3,X2] : (~r2_hidden(X2,k2_relat_1(X3)) | ~v1_xboole_0(X3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | (~spl5_1 | ~spl5_21)),
% 0.20/0.47    inference(resolution,[],[f131,f41])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    ( ! [X2,X3] : (~v1_xboole_0(X3) | ~r2_hidden(X2,k2_relat_1(X3))) ) | ~spl5_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f130])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    spl5_21 | ~spl5_6 | ~spl5_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f128,f118,f59,f130])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl5_6 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl5_19 <=> ! [X0,X2] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ( ! [X2,X3] : (~r2_hidden(X2,k2_relat_1(X3)) | ~v1_xboole_0(X3)) ) | (~spl5_6 | ~spl5_19)),
% 0.20/0.47    inference(resolution,[],[f119,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl5_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) ) | ~spl5_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f118])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl5_20 | ~spl5_11 | ~spl5_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f106,f102,f81,f124])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl5_11 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl5_16 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(X0) | ~v1_xboole_0(k1_relat_1(X0))) ) | (~spl5_11 | ~spl5_16)),
% 0.20/0.47    inference(resolution,[],[f103,f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X0] : (v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_relat_1(X0))) ) | ~spl5_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f81])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f102])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl5_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f118])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.47    inference(equality_resolution,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl5_16 | ~spl5_6 | ~spl5_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f96,f85,f59,f102])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl5_6 | ~spl5_12)),
% 0.20/0.47    inference(resolution,[],[f86,f60])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl5_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f89])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl5_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f85])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl5_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f23,f81])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0] : (v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl5_10 | ~spl5_4 | ~spl5_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f74,f63,f51,f77])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl5_4 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl5_7 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    v1_relat_1(k1_xboole_0) | (~spl5_4 | ~spl5_7)),
% 0.20/0.47    inference(superposition,[],[f52,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl5_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f51])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl5_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f63])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl5_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f59])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl5_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f55])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f51])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ~spl5_2 | ~spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f47,f44])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f40])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (17088)------------------------------
% 0.20/0.47  % (17088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (17088)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (17088)Memory used [KB]: 10746
% 0.20/0.47  % (17088)Time elapsed: 0.064 s
% 0.20/0.47  % (17088)------------------------------
% 0.20/0.47  % (17088)------------------------------
% 0.20/0.48  % (17077)Success in time 0.12 s
%------------------------------------------------------------------------------
