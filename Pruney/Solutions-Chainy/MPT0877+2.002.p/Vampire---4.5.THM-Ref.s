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
% DateTime   : Thu Dec  3 12:58:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 333 expanded)
%              Number of leaves         :   21 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  285 (1063 expanded)
%              Number of equality atoms :  168 ( 905 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f96,f106,f119,f123,f124,f142,f161,f170,f196,f203,f216,f224,f228,f235,f251,f266])).

fof(f266,plain,
    ( spl6_17
    | spl6_18
    | spl6_2
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f263,f226,f30,f182,f179])).

fof(f179,plain,
    ( spl6_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f182,plain,
    ( spl6_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f30,plain,
    ( spl6_2
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f226,plain,
    ( spl6_23
  <=> sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f263,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_23 ),
    inference(superposition,[],[f20,f227])).

fof(f227,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f226])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f251,plain,(
    ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl6_18 ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_18 ),
    inference(superposition,[],[f248,f25])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f248,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f241,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f241,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f22,f183])).

fof(f183,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f22,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f14,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f235,plain,
    ( spl6_17
    | spl6_18
    | spl6_1
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f232,f222,f27,f182,f179])).

fof(f27,plain,
    ( spl6_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f222,plain,
    ( spl6_22
  <=> sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f232,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_22 ),
    inference(superposition,[],[f19,f223])).

fof(f223,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f228,plain,
    ( spl6_8
    | spl6_9
    | spl6_23
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f219,f213,f226,f63,f60])).

fof(f60,plain,
    ( spl6_8
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f63,plain,
    ( spl6_9
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f213,plain,
    ( spl6_21
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f219,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl6_21 ),
    inference(superposition,[],[f20,f214])).

fof(f214,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f213])).

fof(f224,plain,
    ( spl6_8
    | spl6_9
    | spl6_22
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f218,f213,f222,f63,f60])).

fof(f218,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl6_21 ),
    inference(superposition,[],[f19,f214])).

fof(f216,plain,
    ( spl6_12
    | spl6_13
    | spl6_21
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f211,f46,f213,f86,f83])).

fof(f83,plain,
    ( spl6_12
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f86,plain,
    ( spl6_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f46,plain,
    ( spl6_6
  <=> k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f211,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_6 ),
    inference(superposition,[],[f19,f47])).

fof(f47,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f203,plain,(
    ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl6_17 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_17 ),
    inference(superposition,[],[f200,f25])).

fof(f200,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f198,f25])).

fof(f198,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2)
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f22,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f179])).

fof(f196,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl6_12 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_12 ),
    inference(superposition,[],[f193,f25])).

fof(f193,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f22,f84])).

fof(f84,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f170,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f22,f164])).

fof(f164,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f163,f25])).

fof(f163,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f162,f24])).

fof(f162,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0),sK5)
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f23,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f23,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f13,f21,f21])).

fof(f13,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f161,plain,(
    ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl6_13 ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_13 ),
    inference(superposition,[],[f156,f24])).

fof(f156,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f22,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f142,plain,
    ( spl6_9
    | spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f138,f40,f60,f63])).

fof(f40,plain,
    ( spl6_4
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f138,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl6_4 ),
    inference(superposition,[],[f16,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f124,plain,
    ( spl6_4
    | spl6_5
    | spl6_7 ),
    inference(avatar_split_clause,[],[f121,f50,f43,f40])).

fof(f43,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f50,plain,
    ( spl6_7
  <=> sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f121,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f20,f23])).

fof(f123,plain,
    ( spl6_4
    | spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f120,f46,f43,f40])).

fof(f120,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f19,f23])).

fof(f119,plain,
    ( spl6_13
    | spl6_12
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f115,f60,f83,f86])).

fof(f115,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(superposition,[],[f16,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f109,f25])).

fof(f109,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f107,f25])).

fof(f107,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4),sK5)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f23,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f106,plain,
    ( spl6_12
    | spl6_13
    | spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f103,f50,f33,f86,f83])).

fof(f33,plain,
    ( spl6_3
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f103,plain,
    ( sK2 = sK5
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_7 ),
    inference(superposition,[],[f20,f51])).

fof(f51,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f96,plain,
    ( spl6_13
    | spl6_12
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f80,f43,f83,f86])).

fof(f80,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl6_5 ),
    inference(superposition,[],[f16,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f74,f24])).

fof(f74,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f23,f44])).

fof(f44,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f35,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f15,f33,f30,f27])).

fof(f15,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:52:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (23977)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (23985)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (23977)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f267,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f35,f96,f106,f119,f123,f124,f142,f161,f170,f196,f203,f216,f224,f228,f235,f251,f266])).
% 0.20/0.54  fof(f266,plain,(
% 0.20/0.54    spl6_17 | spl6_18 | spl6_2 | ~spl6_23),
% 0.20/0.54    inference(avatar_split_clause,[],[f263,f226,f30,f182,f179])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    spl6_17 <=> k1_xboole_0 = sK0),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.54  fof(f182,plain,(
% 0.20/0.54    spl6_18 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    spl6_2 <=> sK1 = sK4),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.54  fof(f226,plain,(
% 0.20/0.54    spl6_23 <=> sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.54  fof(f263,plain,(
% 0.20/0.54    sK1 = sK4 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_23),
% 0.20/0.54    inference(superposition,[],[f20,f227])).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl6_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f226])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,plain,(
% 0.20/0.54    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.20/0.54  fof(f251,plain,(
% 0.20/0.54    ~spl6_18),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f250])).
% 0.20/0.54  fof(f250,plain,(
% 0.20/0.54    $false | ~spl6_18),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f249])).
% 0.20/0.54  fof(f249,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | ~spl6_18),
% 0.20/0.54    inference(superposition,[],[f248,f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.54    inference(flattening,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.54  fof(f248,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | ~spl6_18),
% 0.20/0.54    inference(forward_demodulation,[],[f241,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | ~spl6_18),
% 0.20/0.54    inference(backward_demodulation,[],[f22,f183])).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | ~spl6_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f182])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.20/0.54    inference(definition_unfolding,[],[f14,f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    (sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)) => ((sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f7,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 0.20/0.54    inference(flattening,[],[f6])).
% 0.20/0.54  fof(f6,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.54    inference(negated_conjecture,[],[f4])).
% 0.20/0.54  fof(f4,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.20/0.54  fof(f235,plain,(
% 0.20/0.54    spl6_17 | spl6_18 | spl6_1 | ~spl6_22),
% 0.20/0.54    inference(avatar_split_clause,[],[f232,f222,f27,f182,f179])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    spl6_1 <=> sK0 = sK3),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.54  fof(f222,plain,(
% 0.20/0.54    spl6_22 <=> sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    sK0 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_22),
% 0.20/0.54    inference(superposition,[],[f19,f223])).
% 0.20/0.54  fof(f223,plain,(
% 0.20/0.54    sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl6_22),
% 0.20/0.54    inference(avatar_component_clause,[],[f222])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f228,plain,(
% 0.20/0.54    spl6_8 | spl6_9 | spl6_23 | ~spl6_21),
% 0.20/0.54    inference(avatar_split_clause,[],[f219,f213,f226,f63,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    spl6_8 <=> k1_xboole_0 = sK3),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    spl6_9 <=> k1_xboole_0 = sK4),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    spl6_21 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | ~spl6_21),
% 0.20/0.54    inference(superposition,[],[f20,f214])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | ~spl6_21),
% 0.20/0.54    inference(avatar_component_clause,[],[f213])).
% 0.20/0.54  fof(f224,plain,(
% 0.20/0.54    spl6_8 | spl6_9 | spl6_22 | ~spl6_21),
% 0.20/0.54    inference(avatar_split_clause,[],[f218,f213,f222,f63,f60])).
% 0.20/0.54  fof(f218,plain,(
% 0.20/0.54    sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | ~spl6_21),
% 0.20/0.54    inference(superposition,[],[f19,f214])).
% 0.20/0.54  fof(f216,plain,(
% 0.20/0.54    spl6_12 | spl6_13 | spl6_21 | ~spl6_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f211,f46,f213,f86,f83])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    spl6_12 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    spl6_13 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    spl6_6 <=> k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.54  fof(f211,plain,(
% 0.20/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_6),
% 0.20/0.54    inference(superposition,[],[f19,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f46])).
% 0.20/0.54  fof(f203,plain,(
% 0.20/0.54    ~spl6_17),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f202])).
% 0.20/0.54  fof(f202,plain,(
% 0.20/0.54    $false | ~spl6_17),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f201])).
% 0.20/0.54  fof(f201,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | ~spl6_17),
% 0.20/0.54    inference(superposition,[],[f200,f25])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | ~spl6_17),
% 0.20/0.54    inference(forward_demodulation,[],[f198,f25])).
% 0.20/0.54  fof(f198,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2) | ~spl6_17),
% 0.20/0.54    inference(backward_demodulation,[],[f22,f180])).
% 0.20/0.54  fof(f180,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | ~spl6_17),
% 0.20/0.54    inference(avatar_component_clause,[],[f179])).
% 0.20/0.54  fof(f196,plain,(
% 0.20/0.54    ~spl6_12),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f195])).
% 0.20/0.54  fof(f195,plain,(
% 0.20/0.54    $false | ~spl6_12),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f194])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | ~spl6_12),
% 0.20/0.54    inference(superposition,[],[f193,f25])).
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | ~spl6_12),
% 0.20/0.54    inference(forward_demodulation,[],[f22,f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f83])).
% 0.20/0.54  fof(f170,plain,(
% 0.20/0.54    ~spl6_9),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.54  fof(f165,plain,(
% 0.20/0.54    $false | ~spl6_9),
% 0.20/0.54    inference(subsumption_resolution,[],[f22,f164])).
% 0.20/0.54  fof(f164,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_9),
% 0.20/0.54    inference(forward_demodulation,[],[f163,f25])).
% 0.20/0.54  fof(f163,plain,(
% 0.20/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5) | ~spl6_9),
% 0.20/0.54    inference(forward_demodulation,[],[f162,f24])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0),sK5) | ~spl6_9),
% 0.20/0.54    inference(forward_demodulation,[],[f23,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    k1_xboole_0 = sK4 | ~spl6_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f63])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 0.20/0.54    inference(definition_unfolding,[],[f13,f21,f21])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    ~spl6_13),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f160])).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    $false | ~spl6_13),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f159])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | ~spl6_13),
% 0.20/0.54    inference(superposition,[],[f156,f24])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | ~spl6_13),
% 0.20/0.54    inference(backward_demodulation,[],[f22,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~spl6_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f86])).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    spl6_9 | spl6_8 | ~spl6_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f138,f40,f60,f63])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    spl6_4 <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl6_4),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f137])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl6_4),
% 0.20/0.54    inference(superposition,[],[f16,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl6_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f40])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    spl6_4 | spl6_5 | spl6_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f121,f50,f43,f40])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    spl6_5 <=> k1_xboole_0 = sK5),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    spl6_7 <=> sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.20/0.54    inference(superposition,[],[f20,f23])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    spl6_4 | spl6_5 | spl6_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f120,f46,f43,f40])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.20/0.54    inference(superposition,[],[f19,f23])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    spl6_13 | spl6_12 | ~spl6_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f115,f60,f83,f86])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl6_8),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f114])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl6_8),
% 0.20/0.54    inference(superposition,[],[f16,f110])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_8),
% 0.20/0.54    inference(forward_demodulation,[],[f109,f25])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5) | ~spl6_8),
% 0.20/0.54    inference(forward_demodulation,[],[f107,f25])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4),sK5) | ~spl6_8),
% 0.20/0.54    inference(backward_demodulation,[],[f23,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    k1_xboole_0 = sK3 | ~spl6_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f60])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    spl6_12 | spl6_13 | spl6_3 | ~spl6_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f103,f50,f33,f86,f83])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    spl6_3 <=> sK2 = sK5),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    sK2 = sK5 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_7),
% 0.20/0.54    inference(superposition,[],[f20,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f50])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    spl6_13 | spl6_12 | ~spl6_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f80,f43,f83,f86])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl6_5),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl6_5),
% 0.20/0.54    inference(superposition,[],[f16,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_5),
% 0.20/0.54    inference(forward_demodulation,[],[f74,f24])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0) | ~spl6_5),
% 0.20/0.54    inference(forward_demodulation,[],[f23,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    k1_xboole_0 = sK5 | ~spl6_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f43])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f15,f33,f30,f27])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (23977)------------------------------
% 0.20/0.54  % (23977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23977)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (23977)Memory used [KB]: 10746
% 0.20/0.54  % (23977)Time elapsed: 0.101 s
% 0.20/0.54  % (23977)------------------------------
% 0.20/0.54  % (23977)------------------------------
% 0.20/0.54  % (23974)Success in time 0.18 s
%------------------------------------------------------------------------------
