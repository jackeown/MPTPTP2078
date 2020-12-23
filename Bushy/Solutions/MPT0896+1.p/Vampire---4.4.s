%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t56_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  316 ( 838 expanded)
%              Number of leaves         :   62 ( 378 expanded)
%              Depth                    :   11
%              Number of atoms          : 1015 (2535 expanded)
%              Number of equality atoms :  424 (1506 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f603,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f63,f70,f77,f84,f109,f131,f140,f143,f153,f172,f177,f186,f198,f205,f212,f216,f218,f237,f245,f253,f261,f265,f266,f270,f275,f276,f286,f287,f290,f299,f302,f304,f306,f320,f327,f328,f332,f333,f340,f342,f350,f356,f389,f393,f397,f404,f406,f408,f412,f413,f427,f429,f431,f441,f444,f470,f471,f482,f489,f493,f497,f499,f503,f506,f508,f543,f544,f555,f562,f602])).

fof(f602,plain,
    ( spl8_5
    | spl8_7
    | spl8_13
    | spl8_29
    | ~ spl8_72 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_29
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f600,f96])).

fof(f96,plain,
    ( sK2 != sK6
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_13
  <=> sK2 != sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f600,plain,
    ( sK2 = sK6
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_29
    | ~ spl8_72 ),
    inference(equality_resolution,[],[f595])).

fof(f595,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK6 = X17 )
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_29
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f594,f156])).

fof(f156,plain,
    ( k1_xboole_0 != sK6
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_29
  <=> k1_xboole_0 != sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f594,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK6
        | sK6 = X17 )
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f593,f69])).

fof(f69,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl8_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f593,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK6
        | sK6 = X17 )
    | ~ spl8_7
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f584,f76])).

fof(f76,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_7
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f584,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK6
        | sK6 = X17 )
    | ~ spl8_72 ),
    inference(superposition,[],[f41,f554])).

fof(f554,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK1,sK6)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl8_72
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK1,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t36_mcart_1)).

fof(f562,plain,
    ( ~ spl8_75
    | ~ spl8_14
    | spl8_69 ),
    inference(avatar_split_clause,[],[f547,f487,f98,f560])).

fof(f560,plain,
    ( spl8_75
  <=> k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f98,plain,
    ( spl8_14
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f487,plain,
    ( spl8_69
  <=> k1_xboole_0 != k3_zfmisc_1(sK0,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f547,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK6)
    | ~ spl8_14
    | ~ spl8_69 ),
    inference(backward_demodulation,[],[f99,f488])).

fof(f488,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK5,sK6)
    | ~ spl8_69 ),
    inference(avatar_component_clause,[],[f487])).

fof(f99,plain,
    ( sK1 = sK5
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f555,plain,
    ( spl8_72
    | ~ spl8_14
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f546,f480,f98,f553])).

fof(f480,plain,
    ( spl8_66
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f546,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK1,sK6)
    | ~ spl8_14
    | ~ spl8_66 ),
    inference(backward_demodulation,[],[f99,f481])).

fof(f481,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK5,sK6)
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f480])).

fof(f544,plain,
    ( spl8_14
    | spl8_7
    | spl8_29
    | spl8_31
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f541,f480,f161,f155,f75,f98])).

fof(f161,plain,
    ( spl8_31
  <=> k1_xboole_0 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f541,plain,
    ( sK1 = sK5
    | ~ spl8_7
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_66 ),
    inference(equality_resolution,[],[f531])).

fof(f531,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK5 = X16 )
    | ~ spl8_7
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f530,f156])).

fof(f530,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK6
        | sK5 = X16 )
    | ~ spl8_7
    | ~ spl8_31
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f529,f162])).

fof(f162,plain,
    ( k1_xboole_0 != sK5
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f161])).

fof(f529,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | sK5 = X16 )
    | ~ spl8_7
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f520,f76])).

fof(f520,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | sK5 = X16 )
    | ~ spl8_66 ),
    inference(superposition,[],[f40,f481])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f543,plain,
    ( spl8_7
    | spl8_15
    | spl8_29
    | spl8_31
    | ~ spl8_66 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_15
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f541,f102])).

fof(f102,plain,
    ( sK1 != sK5
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_15
  <=> sK1 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f508,plain,
    ( spl8_66
    | ~ spl8_16
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f507,f184,f104,f480])).

fof(f104,plain,
    ( spl8_16
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f184,plain,
    ( spl8_34
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f507,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK5,sK6)
    | ~ spl8_16
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f185,f105])).

fof(f105,plain,
    ( sK0 = sK4
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f185,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f184])).

fof(f506,plain,
    ( ~ spl8_69
    | ~ spl8_16
    | spl8_21 ),
    inference(avatar_split_clause,[],[f505,f123,f104,f487])).

fof(f123,plain,
    ( spl8_21
  <=> k1_xboole_0 != k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f505,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK5,sK6)
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f124,f105])).

fof(f124,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f123])).

fof(f503,plain,
    ( spl8_21
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl8_21
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f501,f49])).

fof(f49,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t35_mcart_1)).

fof(f501,plain,
    ( k1_xboole_0 != k3_zfmisc_1(k1_xboole_0,sK5,sK6)
    | ~ spl8_21
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f124,f171])).

fof(f171,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl8_32
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f499,plain,
    ( spl8_28
    | spl8_32
    | spl8_70
    | spl8_31
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f498,f184,f161,f491,f170,f158])).

fof(f158,plain,
    ( spl8_28
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f491,plain,
    ( spl8_70
  <=> ! [X16,X15,X17] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK4 = X15 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f498,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK6
        | sK4 = X15 )
    | ~ spl8_31
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f452,f162])).

fof(f452,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | sK4 = X15 )
    | ~ spl8_34 ),
    inference(superposition,[],[f39,f185])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f497,plain,
    ( spl8_21
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f496])).

fof(f496,plain,
    ( $false
    | ~ spl8_21
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f495,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f495,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK4,sK5,k1_xboole_0)
    | ~ spl8_21
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f124,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f158])).

fof(f493,plain,
    ( spl8_28
    | spl8_70
    | spl8_31
    | spl8_33
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f462,f184,f167,f161,f491,f158])).

fof(f167,plain,
    ( spl8_33
  <=> k1_xboole_0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f462,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK6
        | sK4 = X15 )
    | ~ spl8_31
    | ~ spl8_33
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f461,f162])).

fof(f461,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | sK4 = X15 )
    | ~ spl8_33
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f452,f168])).

fof(f168,plain,
    ( k1_xboole_0 != sK4
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f167])).

fof(f489,plain,
    ( ~ spl8_69
    | ~ spl8_16
    | spl8_21 ),
    inference(avatar_split_clause,[],[f474,f123,f104,f487])).

fof(f474,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK5,sK6)
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(backward_demodulation,[],[f105,f124])).

fof(f482,plain,
    ( spl8_66
    | ~ spl8_16
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f473,f184,f104,f480])).

fof(f473,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK5,sK6)
    | ~ spl8_16
    | ~ spl8_34 ),
    inference(backward_demodulation,[],[f105,f185])).

fof(f471,plain,
    ( spl8_16
    | spl8_29
    | spl8_31
    | spl8_33
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f468,f184,f167,f161,f155,f104])).

fof(f468,plain,
    ( sK0 = sK4
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_33
    | ~ spl8_34 ),
    inference(equality_resolution,[],[f463])).

fof(f463,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK4 = X15 )
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_33
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f462,f156])).

fof(f470,plain,
    ( spl8_17
    | spl8_29
    | spl8_31
    | spl8_33
    | ~ spl8_34 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl8_17
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_33
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f468,f108])).

fof(f108,plain,
    ( sK0 != sK4
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_17
  <=> sK0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f444,plain,
    ( ~ spl8_65
    | ~ spl8_10
    | spl8_49 ),
    inference(avatar_split_clause,[],[f443,f259,f86,f439])).

fof(f439,plain,
    ( spl8_65
  <=> k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f86,plain,
    ( spl8_10
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f259,plain,
    ( spl8_49
  <=> k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f443,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_10
    | ~ spl8_49 ),
    inference(forward_demodulation,[],[f260,f87])).

fof(f87,plain,
    ( sK3 = sK7
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f260,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f259])).

fof(f441,plain,
    ( ~ spl8_65
    | ~ spl8_10
    | spl8_27 ),
    inference(avatar_split_clause,[],[f434,f148,f86,f439])).

fof(f148,plain,
    ( spl8_27
  <=> k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f434,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_10
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f149,f87])).

fof(f149,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f148])).

fof(f431,plain,
    ( spl8_60
    | ~ spl8_22
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f430,f184,f129,f395])).

fof(f395,plain,
    ( spl8_60
  <=> ! [X3,X2] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k3_zfmisc_1(sK0,sK1,sK2) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f129,plain,
    ( spl8_22
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k3_zfmisc_1(sK4,sK5,sK6) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f430,plain,
    ( ! [X0,X1] :
        ( k3_zfmisc_1(sK0,sK1,sK2) = X0
        | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) )
    | ~ spl8_22
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f130,f185])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k3_zfmisc_1(sK4,sK5,sK6) = X0 )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f129])).

fof(f429,plain,
    ( ~ spl8_37
    | spl8_25
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f428,f184,f135,f196])).

fof(f196,plain,
    ( spl8_37
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f135,plain,
    ( spl8_25
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f428,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_25
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f136,f185])).

fof(f136,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f135])).

fof(f427,plain,
    ( spl8_1
    | ~ spl8_36
    | spl8_41 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_36
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f425,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK3
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl8_1
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f425,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_1
    | ~ spl8_36
    | ~ spl8_41 ),
    inference(equality_resolution,[],[f423])).

fof(f423,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(X4,X5) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
        | sK3 = X5 )
    | ~ spl8_1
    | ~ spl8_36
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f422,f55])).

fof(f422,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(X4,X5) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
        | k1_xboole_0 = sK3
        | sK3 = X5 )
    | ~ spl8_36
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f417,f211])).

fof(f211,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl8_41
  <=> k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f417,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(X4,X5) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
        | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
        | k1_xboole_0 = sK3
        | sK3 = X5 )
    | ~ spl8_36 ),
    inference(superposition,[],[f38,f194])).

fof(f194,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl8_36
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t134_zfmisc_1)).

fof(f413,plain,
    ( ~ spl8_51
    | ~ spl8_18
    | spl8_57 ),
    inference(avatar_split_clause,[],[f410,f348,f120,f284])).

fof(f284,plain,
    ( spl8_51
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f120,plain,
    ( spl8_18
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f348,plain,
    ( spl8_57
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f410,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_18
    | ~ spl8_57 ),
    inference(backward_demodulation,[],[f121,f349])).

fof(f349,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f348])).

fof(f121,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f412,plain,
    ( spl8_36
    | ~ spl8_18
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f409,f203,f120,f193])).

fof(f203,plain,
    ( spl8_38
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f409,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_18
    | ~ spl8_38 ),
    inference(backward_demodulation,[],[f121,f204])).

fof(f204,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f203])).

fof(f408,plain,
    ( spl8_36
    | ~ spl8_24
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f407,f184,f138,f193])).

fof(f138,plain,
    ( spl8_24
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f407,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_24
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f139,f185])).

fof(f139,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f138])).

fof(f406,plain,
    ( ~ spl8_51
    | ~ spl8_44
    | spl8_47 ),
    inference(avatar_split_clause,[],[f405,f251,f240,f284])).

fof(f240,plain,
    ( spl8_44
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f251,plain,
    ( spl8_47
  <=> k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f405,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_44
    | ~ spl8_47 ),
    inference(forward_demodulation,[],[f252,f241])).

fof(f241,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f240])).

fof(f252,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f251])).

fof(f404,plain,
    ( ~ spl8_63
    | ~ spl8_34
    | spl8_53 ),
    inference(avatar_split_clause,[],[f353,f315,f184,f402])).

fof(f402,plain,
    ( spl8_63
  <=> k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f315,plain,
    ( spl8_53
  <=> k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f353,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_34
    | ~ spl8_53 ),
    inference(forward_demodulation,[],[f316,f185])).

fof(f316,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f315])).

fof(f397,plain,
    ( spl8_18
    | spl8_60
    | ~ spl8_38
    | spl8_41 ),
    inference(avatar_split_clause,[],[f363,f210,f203,f395,f120])).

fof(f363,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = sK7
        | k3_zfmisc_1(sK0,sK1,sK2) = X2 )
    | ~ spl8_38
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f362,f211])).

fof(f362,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
        | k1_xboole_0 = sK7
        | k3_zfmisc_1(sK0,sK1,sK2) = X2 )
    | ~ spl8_38 ),
    inference(superposition,[],[f37,f204])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f393,plain,
    ( spl8_18
    | spl8_58
    | ~ spl8_38
    | spl8_41 ),
    inference(avatar_split_clause,[],[f384,f210,f203,f391,f120])).

fof(f391,plain,
    ( spl8_58
  <=> ! [X5,X4] :
        ( k2_zfmisc_1(X4,X5) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | sK7 = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f384,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(X4,X5) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = sK7
        | sK7 = X5 )
    | ~ spl8_38
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f378,f211])).

fof(f378,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(X4,X5) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
        | k1_xboole_0 = sK7
        | sK7 = X5 )
    | ~ spl8_38 ),
    inference(superposition,[],[f38,f204])).

fof(f389,plain,
    ( spl8_11
    | spl8_19
    | ~ spl8_38
    | spl8_41 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_19
    | ~ spl8_38
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f387,f90])).

fof(f90,plain,
    ( sK3 != sK7
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_11
  <=> sK3 != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f387,plain,
    ( sK3 = sK7
    | ~ spl8_19
    | ~ spl8_38
    | ~ spl8_41 ),
    inference(equality_resolution,[],[f385])).

fof(f385,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(X4,X5) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | sK7 = X5 )
    | ~ spl8_19
    | ~ spl8_38
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f384,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK7
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_19
  <=> k1_xboole_0 != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f356,plain,
    ( spl8_38
    | ~ spl8_8
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f355,f184,f82,f203])).

fof(f82,plain,
    ( spl8_8
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f355,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_8
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f83,f185])).

fof(f83,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f350,plain,
    ( ~ spl8_57
    | ~ spl8_44
    | spl8_49 ),
    inference(avatar_split_clause,[],[f343,f259,f240,f348])).

fof(f343,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_44
    | ~ spl8_49 ),
    inference(forward_demodulation,[],[f260,f241])).

fof(f342,plain,
    ( spl8_50
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f341,f248,f240,f281])).

fof(f281,plain,
    ( spl8_50
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f248,plain,
    ( spl8_46
  <=> k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f341,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f249,f241])).

fof(f249,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f248])).

fof(f340,plain,
    ( ~ spl8_43
    | spl8_27
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f339,f240,f148,f235])).

fof(f235,plain,
    ( spl8_43
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f339,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_27
    | ~ spl8_44 ),
    inference(forward_demodulation,[],[f149,f241])).

fof(f333,plain,
    ( spl8_34
    | spl8_40
    | spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f300,f82,f54,f207,f184])).

fof(f207,plain,
    ( spl8_40
  <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f300,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f295,f55])).

fof(f295,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_8 ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k3_zfmisc_1(sK4,sK5,sK6) = X0 )
    | ~ spl8_8 ),
    inference(superposition,[],[f37,f83])).

fof(f332,plain,
    ( spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_40 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f330,f62])).

fof(f62,plain,
    ( k1_xboole_0 != sK2
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_3
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f330,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f329,f69])).

fof(f329,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl8_7
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f313,f76])).

fof(f313,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl8_40 ),
    inference(trivial_inequality_removal,[],[f312])).

fof(f312,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl8_40 ),
    inference(superposition,[],[f42,f208])).

fof(f208,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f207])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f328,plain,
    ( ~ spl8_55
    | ~ spl8_40
    | spl8_43 ),
    inference(avatar_split_clause,[],[f311,f235,f207,f325])).

fof(f325,plain,
    ( spl8_55
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f311,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_40
    | ~ spl8_43 ),
    inference(backward_demodulation,[],[f208,f236])).

fof(f236,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f235])).

fof(f327,plain,
    ( ~ spl8_55
    | spl8_37
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f310,f207,f196,f325])).

fof(f310,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_37
    | ~ spl8_40 ),
    inference(backward_demodulation,[],[f208,f197])).

fof(f197,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f196])).

fof(f320,plain,
    ( spl8_52
    | ~ spl8_24
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f308,f207,f138,f318])).

fof(f318,plain,
    ( spl8_52
  <=> k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f308,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0)
    | ~ spl8_24
    | ~ spl8_40 ),
    inference(backward_demodulation,[],[f208,f139])).

fof(f306,plain,
    ( spl8_50
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f305,f248,f120,f281])).

fof(f305,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f249,f121])).

fof(f304,plain,
    ( spl8_50
    | ~ spl8_18
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f303,f256,f120,f281])).

fof(f256,plain,
    ( spl8_48
  <=> k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f303,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_18
    | ~ spl8_48 ),
    inference(forward_demodulation,[],[f257,f121])).

fof(f257,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f256])).

fof(f302,plain,
    ( spl8_40
    | spl8_1
    | ~ spl8_8
    | spl8_35 ),
    inference(avatar_split_clause,[],[f301,f181,f82,f54,f207])).

fof(f181,plain,
    ( spl8_35
  <=> k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f301,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f300,f182])).

fof(f182,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f181])).

fof(f299,plain,
    ( spl8_1
    | ~ spl8_8
    | spl8_35
    | spl8_41 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_35
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f297,f182])).

fof(f297,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f296,f55])).

fof(f296,plain,
    ( k1_xboole_0 = sK3
    | k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_8
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f295,f211])).

fof(f290,plain,
    ( spl8_24
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f289,f120,f82,f138])).

fof(f289,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0)
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f83,f121])).

fof(f287,plain,
    ( ~ spl8_51
    | ~ spl8_18
    | spl8_49 ),
    inference(avatar_split_clause,[],[f279,f259,f120,f284])).

fof(f279,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_18
    | ~ spl8_49 ),
    inference(backward_demodulation,[],[f121,f260])).

fof(f286,plain,
    ( ~ spl8_51
    | ~ spl8_18
    | spl8_47 ),
    inference(avatar_split_clause,[],[f278,f251,f120,f284])).

fof(f278,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_18
    | ~ spl8_47 ),
    inference(backward_demodulation,[],[f121,f252])).

fof(f276,plain,
    ( spl8_18
    | spl8_20
    | spl8_22
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f174,f82,f129,f126,f120])).

fof(f126,plain,
    ( spl8_20
  <=> k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f174,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
        | k1_xboole_0 = sK7
        | k3_zfmisc_1(sK4,sK5,sK6) = X2 )
    | ~ spl8_8 ),
    inference(superposition,[],[f37,f83])).

fof(f275,plain,
    ( spl8_21
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl8_21
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f273,f48])).

fof(f48,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f273,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK4,k1_xboole_0,sK6)
    | ~ spl8_21
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f124,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_30
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f270,plain,
    ( ~ spl8_30
    | ~ spl8_34
    | spl8_41 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl8_30
    | ~ spl8_34
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f268,f211])).

fof(f268,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_30
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f267,f48])).

fof(f267,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,k1_xboole_0,sK6)
    | ~ spl8_30
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f185,f165])).

fof(f266,plain,
    ( spl8_26
    | ~ spl8_8
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f228,f164,f82,f151])).

fof(f151,plain,
    ( spl8_26
  <=> k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f228,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_8
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f227,f48])).

fof(f227,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,k1_xboole_0,sK6),sK7)
    | ~ spl8_8
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f83,f165])).

fof(f265,plain,
    ( spl8_1
    | ~ spl8_26
    | spl8_41 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_26
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f263,f211])).

fof(f263,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_1
    | ~ spl8_26
    | ~ spl8_41 ),
    inference(equality_resolution,[],[f226])).

fof(f226,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(X2,X3)
        | k3_zfmisc_1(sK0,sK1,sK2) = X2 )
    | ~ spl8_1
    | ~ spl8_26
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f225,f55])).

fof(f225,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = sK3
        | k3_zfmisc_1(sK0,sK1,sK2) = X2 )
    | ~ spl8_26
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f224,f211])).

fof(f224,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
        | k1_xboole_0 = sK3
        | k3_zfmisc_1(sK0,sK1,sK2) = X2 )
    | ~ spl8_26 ),
    inference(superposition,[],[f37,f152])).

fof(f152,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f151])).

fof(f261,plain,
    ( ~ spl8_49
    | ~ spl8_26
    | spl8_39 ),
    inference(avatar_split_clause,[],[f254,f200,f151,f259])).

fof(f200,plain,
    ( spl8_39
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f254,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_26
    | ~ spl8_39 ),
    inference(forward_demodulation,[],[f201,f152])).

fof(f201,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f200])).

fof(f253,plain,
    ( ~ spl8_47
    | ~ spl8_26
    | spl8_37 ),
    inference(avatar_split_clause,[],[f246,f196,f151,f251])).

fof(f246,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_26
    | ~ spl8_37 ),
    inference(forward_demodulation,[],[f197,f152])).

fof(f245,plain,
    ( ~ spl8_45
    | ~ spl8_26
    | spl8_43 ),
    inference(avatar_split_clause,[],[f238,f235,f151,f243])).

fof(f243,plain,
    ( spl8_45
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f238,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_26
    | ~ spl8_43 ),
    inference(superposition,[],[f236,f152])).

fof(f237,plain,
    ( ~ spl8_43
    | spl8_25
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f230,f164,f135,f235])).

fof(f230,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_25
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f229,f48])).

fof(f229,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) != k2_zfmisc_1(k3_zfmisc_1(sK4,k1_xboole_0,sK6),k1_xboole_0)
    | ~ spl8_25
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f136,f165])).

fof(f218,plain,
    ( spl8_20
    | spl8_22
    | ~ spl8_8
    | spl8_19 ),
    inference(avatar_split_clause,[],[f217,f117,f82,f129,f126])).

fof(f217,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
        | k3_zfmisc_1(sK4,sK5,sK6) = X2 )
    | ~ spl8_8
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f174,f118])).

fof(f216,plain,
    ( ~ spl8_41
    | spl8_29
    | spl8_31
    | spl8_33
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f215,f184,f167,f161,f155,f210])).

fof(f215,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_29
    | ~ spl8_31
    | ~ spl8_33
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f214,f156])).

fof(f214,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK6
    | ~ spl8_31
    | ~ spl8_33
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f213,f162])).

fof(f213,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | ~ spl8_33
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f191,f168])).

fof(f191,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | ~ spl8_34 ),
    inference(superposition,[],[f42,f185])).

fof(f212,plain,
    ( ~ spl8_41
    | spl8_21
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f190,f184,f123,f210])).

fof(f190,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_21
    | ~ spl8_34 ),
    inference(superposition,[],[f124,f185])).

fof(f205,plain,
    ( spl8_38
    | ~ spl8_8
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f189,f184,f82,f203])).

fof(f189,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_8
    | ~ spl8_34 ),
    inference(backward_demodulation,[],[f185,f83])).

fof(f198,plain,
    ( ~ spl8_37
    | spl8_25
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f188,f184,f135,f196])).

fof(f188,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_25
    | ~ spl8_34 ),
    inference(backward_demodulation,[],[f185,f136])).

fof(f186,plain,
    ( spl8_34
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f179,f129,f184])).

fof(f179,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_22 ),
    inference(equality_resolution,[],[f130])).

fof(f177,plain,
    ( spl8_22
    | ~ spl8_8
    | spl8_19
    | spl8_21 ),
    inference(avatar_split_clause,[],[f176,f123,f117,f82,f129])).

fof(f176,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k3_zfmisc_1(sK4,sK5,sK6) = X2 )
    | ~ spl8_8
    | ~ spl8_19
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f175,f118])).

fof(f175,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = sK7
        | k3_zfmisc_1(sK4,sK5,sK6) = X2 )
    | ~ spl8_8
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f174,f124])).

fof(f172,plain,
    ( spl8_28
    | spl8_30
    | spl8_32
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f146,f126,f170,f164,f158])).

fof(f146,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | ~ spl8_20 ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | ~ spl8_20 ),
    inference(superposition,[],[f42,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f126])).

fof(f153,plain,
    ( spl8_26
    | ~ spl8_8
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f144,f126,f82,f151])).

fof(f144,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_8
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f127,f83])).

fof(f143,plain,
    ( spl8_18
    | spl8_20
    | spl8_22
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f142,f82,f129,f126,f120])).

fof(f142,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
        | k1_xboole_0 = sK7
        | k3_zfmisc_1(sK4,sK5,sK6) = X2 )
    | ~ spl8_8 ),
    inference(superposition,[],[f37,f83])).

fof(f140,plain,
    ( spl8_24
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f132,f120,f82,f138])).

fof(f132,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0)
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f121,f83])).

fof(f131,plain,
    ( spl8_18
    | spl8_20
    | spl8_22
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f113,f82,f129,f126,f120])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
        | k1_xboole_0 = sK7
        | k3_zfmisc_1(sK4,sK5,sK6) = X0 )
    | ~ spl8_8 ),
    inference(superposition,[],[f37,f83])).

fof(f109,plain,
    ( ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f28,f107,f101,f95,f89])).

fof(f28,plain,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',t56_mcart_1)).

fof(f84,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f46,f82])).

fof(f46,plain,(
    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    inference(definition_unfolding,[],[f29,f35,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t56_mcart_1.p',d4_zfmisc_1)).

fof(f29,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
