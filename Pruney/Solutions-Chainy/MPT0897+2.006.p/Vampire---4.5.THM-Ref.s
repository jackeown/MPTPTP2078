%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:14 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 615 expanded)
%              Number of leaves         :   30 ( 201 expanded)
%              Depth                    :   13
%              Number of atoms          :  506 (1930 expanded)
%              Number of equality atoms :  226 (1552 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f471,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f64,f95,f111,f127,f140,f156,f166,f189,f205,f223,f243,f264,f283,f306,f329,f341,f382,f417,f441,f446,f451,f455,f463,f470])).

fof(f470,plain,
    ( spl8_11
    | spl8_12
    | spl8_4
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f468,f443,f42,f103,f99])).

fof(f99,plain,
    ( spl8_11
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f103,plain,
    ( spl8_12
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f42,plain,
    ( spl8_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f443,plain,
    ( spl8_25
  <=> sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f468,plain,
    ( sK3 = sK7
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_25 ),
    inference(superposition,[],[f21,f445])).

fof(f445,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f443])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f463,plain,
    ( spl8_16
    | spl8_17
    | spl8_3
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f461,f438,f38,f215,f211])).

fof(f211,plain,
    ( spl8_16
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f215,plain,
    ( spl8_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f38,plain,
    ( spl8_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f438,plain,
    ( spl8_24
  <=> sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f461,plain,
    ( sK2 = sK6
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_24 ),
    inference(superposition,[],[f21,f440])).

fof(f440,plain,
    ( sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f438])).

fof(f455,plain,
    ( spl8_22
    | spl8_23
    | spl8_2
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f453,f448,f34,f337,f333])).

fof(f333,plain,
    ( spl8_22
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f337,plain,
    ( spl8_23
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f34,plain,
    ( spl8_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f448,plain,
    ( spl8_26
  <=> sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f453,plain,
    ( sK1 = sK5
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_26 ),
    inference(superposition,[],[f21,f450])).

fof(f450,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f448])).

fof(f451,plain,
    ( spl8_22
    | spl8_20
    | spl8_26
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f436,f219,f30,f448,f276,f333])).

fof(f276,plain,
    ( spl8_20
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f30,plain,
    ( spl8_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f219,plain,
    ( spl8_18
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f436,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK0
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(superposition,[],[f21,f418])).

fof(f418,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK5)
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f221,f31])).

fof(f31,plain,
    ( sK0 = sK4
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f221,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f219])).

fof(f446,plain,
    ( spl8_11
    | spl8_6
    | spl8_25
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f434,f107,f61,f443,f57,f99])).

fof(f57,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f61,plain,
    ( spl8_7
  <=> k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f107,plain,
    ( spl8_13
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f434,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(superposition,[],[f21,f207])).

fof(f207,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK7)
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f26,f206])).

fof(f206,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f63,f180])).

fof(f180,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f63,f109])).

fof(f109,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f107])).

fof(f63,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f26,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f14,f24,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f14,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f441,plain,
    ( spl8_16
    | spl8_9
    | spl8_24
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f433,f219,f107,f61,f438,f77,f211])).

fof(f77,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f433,plain,
    ( sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_18 ),
    inference(superposition,[],[f21,f266])).

fof(f266,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK6)
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f206,f221])).

fof(f417,plain,
    ( ~ spl8_7
    | ~ spl8_13
    | spl8_19
    | ~ spl8_21
    | ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_13
    | spl8_19
    | ~ spl8_21
    | ~ spl8_23 ),
    inference(trivial_inequality_removal,[],[f415])).

fof(f415,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_7
    | ~ spl8_13
    | spl8_19
    | ~ spl8_21
    | ~ spl8_23 ),
    inference(superposition,[],[f273,f411])).

fof(f411,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_21
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f410,f399])).

fof(f399,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f398,f28])).

fof(f28,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f398,plain,
    ( k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,sK3))
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f397,f28])).

fof(f397,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK2) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3))
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f386,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f386,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3))
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_23 ),
    inference(backward_demodulation,[],[f180,f339])).

fof(f339,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f337])).

fof(f410,plain,
    ( sK4 = k1_relat_1(k1_xboole_0)
    | ~ spl8_21
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f393,f27])).

fof(f393,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_21
    | ~ spl8_23 ),
    inference(backward_demodulation,[],[f282,f339])).

fof(f282,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl8_21
  <=> sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f273,plain,
    ( k1_xboole_0 != sK4
    | spl8_19 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl8_19
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f382,plain,
    ( ~ spl8_15
    | ~ spl8_18
    | spl8_19
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl8_15
    | ~ spl8_18
    | spl8_19
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(trivial_inequality_removal,[],[f380])).

fof(f380,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_15
    | ~ spl8_18
    | spl8_19
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(superposition,[],[f273,f375])).

fof(f375,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_15
    | ~ spl8_18
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f368,f364])).

fof(f364,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_15
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f363,f28])).

fof(f363,plain,
    ( k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,sK2))
    | ~ spl8_15
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f349,f28])).

fof(f349,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2))
    | ~ spl8_15
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f265,f335])).

fof(f335,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f333])).

fof(f265,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_15
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f188,f221])).

fof(f188,plain,
    ( k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f186])).

% (25763)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f186,plain,
    ( spl8_15
  <=> k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f368,plain,
    ( sK4 = k1_relat_1(k1_xboole_0)
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f352,f28])).

fof(f352,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f282,f335])).

fof(f341,plain,
    ( spl8_22
    | spl8_23
    | spl8_1
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f331,f280,f30,f337,f333])).

fof(f331,plain,
    ( sK0 = sK4
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_21 ),
    inference(superposition,[],[f20,f282])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f329,plain,
    ( ~ spl8_18
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(trivial_inequality_removal,[],[f327])).

fof(f327,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(superposition,[],[f319,f28])).

fof(f319,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f311,f28])).

fof(f311,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f25,f310])).

fof(f310,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f309,f27])).

fof(f309,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,k1_xboole_0)
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f221,f278])).

fof(f278,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f276])).

fof(f25,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f15,f24])).

fof(f15,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f306,plain,
    ( ~ spl8_18
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(trivial_inequality_removal,[],[f304])).

fof(f304,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(superposition,[],[f296,f28])).

fof(f296,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f289,f28])).

fof(f289,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f25,f288])).

fof(f288,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f286,f28])).

fof(f286,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f221,f274])).

fof(f274,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f272])).

fof(f283,plain,
    ( spl8_19
    | spl8_20
    | spl8_21
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f269,f219,f280,f276,f272])).

fof(f269,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl8_18 ),
    inference(superposition,[],[f20,f221])).

fof(f264,plain,(
    ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl8_17 ),
    inference(trivial_inequality_removal,[],[f262])).

fof(f262,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_17 ),
    inference(superposition,[],[f251,f28])).

fof(f251,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f244,f27])).

fof(f244,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3)
    | ~ spl8_17 ),
    inference(backward_demodulation,[],[f25,f217])).

fof(f217,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f215])).

fof(f243,plain,(
    ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl8_16 ),
    inference(trivial_inequality_removal,[],[f241])).

fof(f241,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_16 ),
    inference(superposition,[],[f231,f28])).

fof(f231,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f224,f28])).

fof(f224,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f25,f213])).

fof(f213,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f211])).

fof(f223,plain,
    ( spl8_16
    | spl8_17
    | spl8_18
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f209,f186,f219,f215,f211])).

fof(f209,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_15 ),
    inference(superposition,[],[f20,f188])).

fof(f205,plain,(
    ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_12 ),
    inference(superposition,[],[f201,f27])).

fof(f201,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f25,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f189,plain,
    ( spl8_8
    | spl8_9
    | spl8_15
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f183,f107,f186,f77,f73])).

fof(f73,plain,
    ( spl8_8
  <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f183,plain,
    ( k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_13 ),
    inference(superposition,[],[f20,f109])).

fof(f166,plain,
    ( spl8_5
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl8_5
    | ~ spl8_9 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_5
    | ~ spl8_9 ),
    inference(superposition,[],[f153,f27])).

fof(f153,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0)
    | spl8_5
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f54,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f54,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f156,plain,(
    ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl8_11 ),
    inference(trivial_inequality_removal,[],[f154])).

% (25743)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f154,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_11 ),
    inference(superposition,[],[f147,f28])).

fof(f147,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f25,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f140,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl8_5 ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_5 ),
    inference(superposition,[],[f25,f130])).

fof(f130,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f129,f28])).

fof(f129,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f26,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f127,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl8_8 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_8 ),
    inference(superposition,[],[f25,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f116,f28])).

fof(f116,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f113,f28])).

fof(f113,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK7)
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f26,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f111,plain,
    ( spl8_11
    | spl8_12
    | spl8_13
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f97,f61,f107,f103,f99])).

fof(f97,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_7 ),
    inference(superposition,[],[f20,f63])).

fof(f95,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl8_6 ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_6 ),
    inference(superposition,[],[f25,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f86,f27])).

fof(f86,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f26,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f64,plain,
    ( spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f51,f61,f57,f53])).

fof(f51,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    inference(superposition,[],[f20,f26])).

fof(f45,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f16,f42,f38,f34,f30])).

fof(f16,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (25757)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (25745)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.51  % (25755)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.51  % (25748)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.52  % (25747)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.52  % (25739)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.52  % (25745)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.53  % (25738)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.53  % (25737)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.53  % (25736)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.53  % (25764)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.53  % (25735)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.53  % (25758)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.54  % (25754)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.54  % (25733)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.54  % (25733)Refutation not found, incomplete strategy% (25733)------------------------------
% 1.31/0.54  % (25733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (25733)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (25733)Memory used [KB]: 1663
% 1.31/0.54  % (25733)Time elapsed: 0.124 s
% 1.31/0.54  % (25733)------------------------------
% 1.31/0.54  % (25733)------------------------------
% 1.31/0.54  % SZS output start Proof for theBenchmark
% 1.31/0.54  fof(f471,plain,(
% 1.31/0.54    $false),
% 1.31/0.54    inference(avatar_sat_refutation,[],[f45,f64,f95,f111,f127,f140,f156,f166,f189,f205,f223,f243,f264,f283,f306,f329,f341,f382,f417,f441,f446,f451,f455,f463,f470])).
% 1.31/0.54  fof(f470,plain,(
% 1.31/0.54    spl8_11 | spl8_12 | spl8_4 | ~spl8_25),
% 1.31/0.54    inference(avatar_split_clause,[],[f468,f443,f42,f103,f99])).
% 1.31/0.54  fof(f99,plain,(
% 1.31/0.54    spl8_11 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.31/0.54  fof(f103,plain,(
% 1.31/0.54    spl8_12 <=> k1_xboole_0 = sK3),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.31/0.54  fof(f42,plain,(
% 1.31/0.54    spl8_4 <=> sK3 = sK7),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.31/0.54  fof(f443,plain,(
% 1.31/0.54    spl8_25 <=> sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.31/0.54  fof(f468,plain,(
% 1.31/0.54    sK3 = sK7 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_25),
% 1.31/0.54    inference(superposition,[],[f21,f445])).
% 1.31/0.54  fof(f445,plain,(
% 1.31/0.54    sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl8_25),
% 1.31/0.54    inference(avatar_component_clause,[],[f443])).
% 1.31/0.54  fof(f21,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.54    inference(cnf_transformation,[],[f9])).
% 1.31/0.54  fof(f9,plain,(
% 1.31/0.54    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.31/0.54    inference(ennf_transformation,[],[f2])).
% 1.31/0.54  fof(f2,axiom,(
% 1.31/0.54    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 1.31/0.54  fof(f463,plain,(
% 1.31/0.54    spl8_16 | spl8_17 | spl8_3 | ~spl8_24),
% 1.31/0.54    inference(avatar_split_clause,[],[f461,f438,f38,f215,f211])).
% 1.31/0.54  fof(f211,plain,(
% 1.31/0.54    spl8_16 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.31/0.54  fof(f215,plain,(
% 1.31/0.54    spl8_17 <=> k1_xboole_0 = sK2),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.31/0.54  fof(f38,plain,(
% 1.31/0.54    spl8_3 <=> sK2 = sK6),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.31/0.54  fof(f438,plain,(
% 1.31/0.54    spl8_24 <=> sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.31/0.54  fof(f461,plain,(
% 1.31/0.54    sK2 = sK6 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_24),
% 1.31/0.54    inference(superposition,[],[f21,f440])).
% 1.31/0.54  fof(f440,plain,(
% 1.31/0.54    sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_24),
% 1.31/0.54    inference(avatar_component_clause,[],[f438])).
% 1.31/0.54  fof(f455,plain,(
% 1.31/0.54    spl8_22 | spl8_23 | spl8_2 | ~spl8_26),
% 1.31/0.54    inference(avatar_split_clause,[],[f453,f448,f34,f337,f333])).
% 1.31/0.54  fof(f333,plain,(
% 1.31/0.54    spl8_22 <=> k1_xboole_0 = sK0),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.31/0.54  fof(f337,plain,(
% 1.31/0.54    spl8_23 <=> k1_xboole_0 = sK1),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.31/0.54  fof(f34,plain,(
% 1.31/0.54    spl8_2 <=> sK1 = sK5),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.31/0.54  fof(f448,plain,(
% 1.31/0.54    spl8_26 <=> sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.31/0.54  fof(f453,plain,(
% 1.31/0.54    sK1 = sK5 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_26),
% 1.31/0.54    inference(superposition,[],[f21,f450])).
% 1.31/0.54  fof(f450,plain,(
% 1.31/0.54    sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl8_26),
% 1.31/0.54    inference(avatar_component_clause,[],[f448])).
% 1.31/0.54  fof(f451,plain,(
% 1.31/0.54    spl8_22 | spl8_20 | spl8_26 | ~spl8_1 | ~spl8_18),
% 1.31/0.54    inference(avatar_split_clause,[],[f436,f219,f30,f448,f276,f333])).
% 1.31/0.54  fof(f276,plain,(
% 1.31/0.54    spl8_20 <=> k1_xboole_0 = sK5),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.31/0.54  fof(f30,plain,(
% 1.31/0.54    spl8_1 <=> sK0 = sK4),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.31/0.54  fof(f219,plain,(
% 1.31/0.54    spl8_18 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.31/0.54  fof(f436,plain,(
% 1.31/0.54    sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK0 | (~spl8_1 | ~spl8_18)),
% 1.31/0.54    inference(superposition,[],[f21,f418])).
% 1.31/0.54  fof(f418,plain,(
% 1.31/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK5) | (~spl8_1 | ~spl8_18)),
% 1.31/0.54    inference(backward_demodulation,[],[f221,f31])).
% 1.31/0.54  fof(f31,plain,(
% 1.31/0.54    sK0 = sK4 | ~spl8_1),
% 1.31/0.54    inference(avatar_component_clause,[],[f30])).
% 1.31/0.54  fof(f221,plain,(
% 1.31/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_18),
% 1.31/0.54    inference(avatar_component_clause,[],[f219])).
% 1.31/0.54  fof(f446,plain,(
% 1.31/0.54    spl8_11 | spl8_6 | spl8_25 | ~spl8_7 | ~spl8_13),
% 1.31/0.54    inference(avatar_split_clause,[],[f434,f107,f61,f443,f57,f99])).
% 1.31/0.54  fof(f57,plain,(
% 1.31/0.54    spl8_6 <=> k1_xboole_0 = sK7),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.31/0.54  fof(f61,plain,(
% 1.31/0.54    spl8_7 <=> k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.31/0.54  fof(f107,plain,(
% 1.31/0.54    spl8_13 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.31/0.54  fof(f434,plain,(
% 1.31/0.54    sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl8_7 | ~spl8_13)),
% 1.31/0.54    inference(superposition,[],[f21,f207])).
% 1.31/0.54  fof(f207,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK7) | (~spl8_7 | ~spl8_13)),
% 1.31/0.54    inference(backward_demodulation,[],[f26,f206])).
% 1.31/0.54  fof(f206,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | (~spl8_7 | ~spl8_13)),
% 1.31/0.54    inference(backward_demodulation,[],[f63,f180])).
% 1.31/0.54  fof(f180,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | (~spl8_7 | ~spl8_13)),
% 1.31/0.54    inference(backward_demodulation,[],[f63,f109])).
% 1.31/0.54  fof(f109,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_13),
% 1.31/0.54    inference(avatar_component_clause,[],[f107])).
% 1.31/0.54  fof(f63,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl8_7),
% 1.31/0.54    inference(avatar_component_clause,[],[f61])).
% 1.31/0.54  fof(f26,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.31/0.54    inference(definition_unfolding,[],[f14,f24,f24])).
% 1.31/0.54  fof(f24,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f23,f22])).
% 1.31/0.54  fof(f22,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f3])).
% 1.31/0.54  fof(f3,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.31/0.54  fof(f23,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.31/0.54  fof(f14,plain,(
% 1.31/0.54    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.31/0.54    inference(cnf_transformation,[],[f11])).
% 1.31/0.54  fof(f11,plain,(
% 1.31/0.54    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f10])).
% 1.31/0.54  fof(f10,plain,(
% 1.31/0.54    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f8,plain,(
% 1.31/0.54    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.31/0.54    inference(flattening,[],[f7])).
% 1.31/0.54  fof(f7,plain,(
% 1.31/0.54    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.31/0.54    inference(ennf_transformation,[],[f6])).
% 1.31/0.54  fof(f6,negated_conjecture,(
% 1.31/0.54    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.54    inference(negated_conjecture,[],[f5])).
% 1.31/0.54  fof(f5,conjecture,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).
% 1.31/0.54  fof(f441,plain,(
% 1.31/0.54    spl8_16 | spl8_9 | spl8_24 | ~spl8_7 | ~spl8_13 | ~spl8_18),
% 1.31/0.54    inference(avatar_split_clause,[],[f433,f219,f107,f61,f438,f77,f211])).
% 1.31/0.54  fof(f77,plain,(
% 1.31/0.54    spl8_9 <=> k1_xboole_0 = sK6),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.31/0.54  fof(f433,plain,(
% 1.31/0.54    sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl8_7 | ~spl8_13 | ~spl8_18)),
% 1.31/0.54    inference(superposition,[],[f21,f266])).
% 1.31/0.54  fof(f266,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK6) | (~spl8_7 | ~spl8_13 | ~spl8_18)),
% 1.31/0.54    inference(backward_demodulation,[],[f206,f221])).
% 1.31/0.54  fof(f417,plain,(
% 1.31/0.54    ~spl8_7 | ~spl8_13 | spl8_19 | ~spl8_21 | ~spl8_23),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f416])).
% 1.31/0.54  fof(f416,plain,(
% 1.31/0.54    $false | (~spl8_7 | ~spl8_13 | spl8_19 | ~spl8_21 | ~spl8_23)),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f415])).
% 1.31/0.54  fof(f415,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | (~spl8_7 | ~spl8_13 | spl8_19 | ~spl8_21 | ~spl8_23)),
% 1.31/0.54    inference(superposition,[],[f273,f411])).
% 1.31/0.54  fof(f411,plain,(
% 1.31/0.54    k1_xboole_0 = sK4 | (~spl8_7 | ~spl8_13 | ~spl8_21 | ~spl8_23)),
% 1.31/0.54    inference(forward_demodulation,[],[f410,f399])).
% 1.31/0.54  fof(f399,plain,(
% 1.31/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl8_7 | ~spl8_13 | ~spl8_23)),
% 1.31/0.54    inference(forward_demodulation,[],[f398,f28])).
% 1.31/0.54  fof(f28,plain,(
% 1.31/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.31/0.54    inference(equality_resolution,[],[f18])).
% 1.31/0.54  fof(f18,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.31/0.54    inference(cnf_transformation,[],[f13])).
% 1.31/0.54  fof(f13,plain,(
% 1.31/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.31/0.54    inference(flattening,[],[f12])).
% 1.31/0.54  fof(f12,plain,(
% 1.31/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.31/0.54    inference(nnf_transformation,[],[f1])).
% 1.31/0.54  fof(f1,axiom,(
% 1.31/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.31/0.54  fof(f398,plain,(
% 1.31/0.54    k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,sK3)) | (~spl8_7 | ~spl8_13 | ~spl8_23)),
% 1.31/0.54    inference(forward_demodulation,[],[f397,f28])).
% 1.31/0.54  fof(f397,plain,(
% 1.31/0.54    k2_zfmisc_1(k1_xboole_0,sK2) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)) | (~spl8_7 | ~spl8_13 | ~spl8_23)),
% 1.31/0.54    inference(forward_demodulation,[],[f386,f27])).
% 1.31/0.54  fof(f27,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.31/0.54    inference(equality_resolution,[],[f19])).
% 1.31/0.54  fof(f19,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f13])).
% 1.31/0.54  fof(f386,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3)) | (~spl8_7 | ~spl8_13 | ~spl8_23)),
% 1.31/0.54    inference(backward_demodulation,[],[f180,f339])).
% 1.31/0.54  fof(f339,plain,(
% 1.31/0.54    k1_xboole_0 = sK1 | ~spl8_23),
% 1.31/0.54    inference(avatar_component_clause,[],[f337])).
% 1.31/0.54  fof(f410,plain,(
% 1.31/0.54    sK4 = k1_relat_1(k1_xboole_0) | (~spl8_21 | ~spl8_23)),
% 1.31/0.54    inference(forward_demodulation,[],[f393,f27])).
% 1.31/0.54  fof(f393,plain,(
% 1.31/0.54    sK4 = k1_relat_1(k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl8_21 | ~spl8_23)),
% 1.31/0.54    inference(backward_demodulation,[],[f282,f339])).
% 1.31/0.54  fof(f282,plain,(
% 1.31/0.54    sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl8_21),
% 1.31/0.54    inference(avatar_component_clause,[],[f280])).
% 1.31/0.54  fof(f280,plain,(
% 1.31/0.54    spl8_21 <=> sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.31/0.54  fof(f273,plain,(
% 1.31/0.54    k1_xboole_0 != sK4 | spl8_19),
% 1.31/0.54    inference(avatar_component_clause,[],[f272])).
% 1.31/0.54  fof(f272,plain,(
% 1.31/0.54    spl8_19 <=> k1_xboole_0 = sK4),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.31/0.54  fof(f382,plain,(
% 1.31/0.54    ~spl8_15 | ~spl8_18 | spl8_19 | ~spl8_21 | ~spl8_22),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f381])).
% 1.31/0.54  fof(f381,plain,(
% 1.31/0.54    $false | (~spl8_15 | ~spl8_18 | spl8_19 | ~spl8_21 | ~spl8_22)),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f380])).
% 1.31/0.54  fof(f380,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | (~spl8_15 | ~spl8_18 | spl8_19 | ~spl8_21 | ~spl8_22)),
% 1.31/0.54    inference(superposition,[],[f273,f375])).
% 1.31/0.54  fof(f375,plain,(
% 1.31/0.54    k1_xboole_0 = sK4 | (~spl8_15 | ~spl8_18 | ~spl8_21 | ~spl8_22)),
% 1.31/0.54    inference(backward_demodulation,[],[f368,f364])).
% 1.31/0.54  fof(f364,plain,(
% 1.31/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl8_15 | ~spl8_18 | ~spl8_22)),
% 1.31/0.54    inference(forward_demodulation,[],[f363,f28])).
% 1.31/0.54  fof(f363,plain,(
% 1.31/0.54    k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,sK2)) | (~spl8_15 | ~spl8_18 | ~spl8_22)),
% 1.31/0.54    inference(forward_demodulation,[],[f349,f28])).
% 1.31/0.54  fof(f349,plain,(
% 1.31/0.54    k2_zfmisc_1(k1_xboole_0,sK1) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2)) | (~spl8_15 | ~spl8_18 | ~spl8_22)),
% 1.31/0.54    inference(backward_demodulation,[],[f265,f335])).
% 1.31/0.54  fof(f335,plain,(
% 1.31/0.54    k1_xboole_0 = sK0 | ~spl8_22),
% 1.31/0.54    inference(avatar_component_clause,[],[f333])).
% 1.31/0.54  fof(f265,plain,(
% 1.31/0.54    k2_zfmisc_1(sK0,sK1) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (~spl8_15 | ~spl8_18)),
% 1.31/0.54    inference(backward_demodulation,[],[f188,f221])).
% 1.31/0.54  fof(f188,plain,(
% 1.31/0.54    k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_15),
% 1.31/0.54    inference(avatar_component_clause,[],[f186])).
% 1.31/0.54  % (25763)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.54  fof(f186,plain,(
% 1.31/0.54    spl8_15 <=> k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.31/0.54  fof(f368,plain,(
% 1.31/0.54    sK4 = k1_relat_1(k1_xboole_0) | (~spl8_21 | ~spl8_22)),
% 1.31/0.54    inference(forward_demodulation,[],[f352,f28])).
% 1.31/0.54  fof(f352,plain,(
% 1.31/0.54    sK4 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl8_21 | ~spl8_22)),
% 1.31/0.54    inference(backward_demodulation,[],[f282,f335])).
% 1.31/0.54  fof(f341,plain,(
% 1.31/0.54    spl8_22 | spl8_23 | spl8_1 | ~spl8_21),
% 1.31/0.54    inference(avatar_split_clause,[],[f331,f280,f30,f337,f333])).
% 1.31/0.54  fof(f331,plain,(
% 1.31/0.54    sK0 = sK4 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_21),
% 1.31/0.54    inference(superposition,[],[f20,f282])).
% 1.31/0.54  fof(f20,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.31/0.54    inference(cnf_transformation,[],[f9])).
% 1.31/0.54  fof(f329,plain,(
% 1.31/0.54    ~spl8_18 | ~spl8_20),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f328])).
% 1.31/0.54  fof(f328,plain,(
% 1.31/0.54    $false | (~spl8_18 | ~spl8_20)),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f327])).
% 1.31/0.54  fof(f327,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | (~spl8_18 | ~spl8_20)),
% 1.31/0.54    inference(superposition,[],[f319,f28])).
% 1.31/0.54  fof(f319,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (~spl8_18 | ~spl8_20)),
% 1.31/0.54    inference(forward_demodulation,[],[f311,f28])).
% 1.31/0.54  fof(f311,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | (~spl8_18 | ~spl8_20)),
% 1.31/0.54    inference(backward_demodulation,[],[f25,f310])).
% 1.31/0.54  fof(f310,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl8_18 | ~spl8_20)),
% 1.31/0.54    inference(forward_demodulation,[],[f309,f27])).
% 1.31/0.54  fof(f309,plain,(
% 1.31/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,k1_xboole_0) | (~spl8_18 | ~spl8_20)),
% 1.31/0.54    inference(backward_demodulation,[],[f221,f278])).
% 1.31/0.54  fof(f278,plain,(
% 1.31/0.54    k1_xboole_0 = sK5 | ~spl8_20),
% 1.31/0.54    inference(avatar_component_clause,[],[f276])).
% 1.31/0.54  fof(f25,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 1.31/0.54    inference(definition_unfolding,[],[f15,f24])).
% 1.31/0.54  fof(f15,plain,(
% 1.31/0.54    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 1.31/0.54    inference(cnf_transformation,[],[f11])).
% 1.31/0.54  fof(f306,plain,(
% 1.31/0.54    ~spl8_18 | ~spl8_19),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f305])).
% 1.31/0.54  fof(f305,plain,(
% 1.31/0.54    $false | (~spl8_18 | ~spl8_19)),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f304])).
% 1.31/0.54  fof(f304,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | (~spl8_18 | ~spl8_19)),
% 1.31/0.54    inference(superposition,[],[f296,f28])).
% 1.31/0.54  fof(f296,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (~spl8_18 | ~spl8_19)),
% 1.31/0.54    inference(forward_demodulation,[],[f289,f28])).
% 1.31/0.54  fof(f289,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | (~spl8_18 | ~spl8_19)),
% 1.31/0.54    inference(backward_demodulation,[],[f25,f288])).
% 1.31/0.54  fof(f288,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl8_18 | ~spl8_19)),
% 1.31/0.54    inference(forward_demodulation,[],[f286,f28])).
% 1.31/0.54  fof(f286,plain,(
% 1.31/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK5) | (~spl8_18 | ~spl8_19)),
% 1.31/0.54    inference(backward_demodulation,[],[f221,f274])).
% 1.31/0.54  fof(f274,plain,(
% 1.31/0.54    k1_xboole_0 = sK4 | ~spl8_19),
% 1.31/0.54    inference(avatar_component_clause,[],[f272])).
% 1.31/0.54  fof(f283,plain,(
% 1.31/0.54    spl8_19 | spl8_20 | spl8_21 | ~spl8_18),
% 1.31/0.54    inference(avatar_split_clause,[],[f269,f219,f280,f276,f272])).
% 1.31/0.54  fof(f269,plain,(
% 1.31/0.54    sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | ~spl8_18),
% 1.31/0.54    inference(superposition,[],[f20,f221])).
% 1.31/0.54  fof(f264,plain,(
% 1.31/0.54    ~spl8_17),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f263])).
% 1.31/0.54  fof(f263,plain,(
% 1.31/0.54    $false | ~spl8_17),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f262])).
% 1.31/0.54  fof(f262,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | ~spl8_17),
% 1.31/0.54    inference(superposition,[],[f251,f28])).
% 1.31/0.54  fof(f251,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | ~spl8_17),
% 1.31/0.54    inference(forward_demodulation,[],[f244,f27])).
% 1.31/0.54  fof(f244,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3) | ~spl8_17),
% 1.31/0.54    inference(backward_demodulation,[],[f25,f217])).
% 1.31/0.54  fof(f217,plain,(
% 1.31/0.54    k1_xboole_0 = sK2 | ~spl8_17),
% 1.31/0.54    inference(avatar_component_clause,[],[f215])).
% 1.31/0.54  fof(f243,plain,(
% 1.31/0.54    ~spl8_16),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f242])).
% 1.31/0.54  fof(f242,plain,(
% 1.31/0.54    $false | ~spl8_16),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f241])).
% 1.31/0.54  fof(f241,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | ~spl8_16),
% 1.31/0.54    inference(superposition,[],[f231,f28])).
% 1.31/0.54  fof(f231,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | ~spl8_16),
% 1.31/0.54    inference(forward_demodulation,[],[f224,f28])).
% 1.31/0.54  fof(f224,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | ~spl8_16),
% 1.31/0.54    inference(backward_demodulation,[],[f25,f213])).
% 1.31/0.54  fof(f213,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_16),
% 1.31/0.54    inference(avatar_component_clause,[],[f211])).
% 1.31/0.54  fof(f223,plain,(
% 1.31/0.54    spl8_16 | spl8_17 | spl8_18 | ~spl8_15),
% 1.31/0.54    inference(avatar_split_clause,[],[f209,f186,f219,f215,f211])).
% 1.31/0.54  fof(f209,plain,(
% 1.31/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_15),
% 1.31/0.54    inference(superposition,[],[f20,f188])).
% 1.31/0.54  fof(f205,plain,(
% 1.31/0.54    ~spl8_12),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f204])).
% 1.31/0.54  fof(f204,plain,(
% 1.31/0.54    $false | ~spl8_12),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f203])).
% 1.31/0.54  fof(f203,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | ~spl8_12),
% 1.31/0.54    inference(superposition,[],[f201,f27])).
% 1.31/0.54  fof(f201,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | ~spl8_12),
% 1.31/0.54    inference(backward_demodulation,[],[f25,f105])).
% 1.31/0.54  fof(f105,plain,(
% 1.31/0.54    k1_xboole_0 = sK3 | ~spl8_12),
% 1.31/0.54    inference(avatar_component_clause,[],[f103])).
% 1.31/0.54  fof(f189,plain,(
% 1.31/0.54    spl8_8 | spl8_9 | spl8_15 | ~spl8_13),
% 1.31/0.54    inference(avatar_split_clause,[],[f183,f107,f186,f77,f73])).
% 1.31/0.54  fof(f73,plain,(
% 1.31/0.54    spl8_8 <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.31/0.54  fof(f183,plain,(
% 1.31/0.54    k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_13),
% 1.31/0.54    inference(superposition,[],[f20,f109])).
% 1.31/0.54  fof(f166,plain,(
% 1.31/0.54    spl8_5 | ~spl8_9),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f165])).
% 1.31/0.54  fof(f165,plain,(
% 1.31/0.54    $false | (spl8_5 | ~spl8_9)),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f164])).
% 1.31/0.54  fof(f164,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | (spl8_5 | ~spl8_9)),
% 1.31/0.54    inference(superposition,[],[f153,f27])).
% 1.31/0.54  fof(f153,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0) | (spl8_5 | ~spl8_9)),
% 1.31/0.54    inference(forward_demodulation,[],[f54,f79])).
% 1.31/0.54  fof(f79,plain,(
% 1.31/0.54    k1_xboole_0 = sK6 | ~spl8_9),
% 1.31/0.54    inference(avatar_component_clause,[],[f77])).
% 1.31/0.54  fof(f54,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | spl8_5),
% 1.31/0.54    inference(avatar_component_clause,[],[f53])).
% 1.31/0.54  fof(f53,plain,(
% 1.31/0.54    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.31/0.54  fof(f156,plain,(
% 1.31/0.54    ~spl8_11),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f155])).
% 1.31/0.54  fof(f155,plain,(
% 1.31/0.54    $false | ~spl8_11),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f154])).
% 1.31/0.54  % (25743)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.54  fof(f154,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | ~spl8_11),
% 1.31/0.54    inference(superposition,[],[f147,f28])).
% 1.31/0.54  fof(f147,plain,(
% 1.31/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | ~spl8_11),
% 1.31/0.54    inference(backward_demodulation,[],[f25,f101])).
% 1.31/0.54  fof(f101,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_11),
% 1.31/0.54    inference(avatar_component_clause,[],[f99])).
% 1.31/0.54  fof(f140,plain,(
% 1.31/0.54    ~spl8_5),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f139])).
% 1.31/0.54  fof(f139,plain,(
% 1.31/0.54    $false | ~spl8_5),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f135])).
% 1.31/0.54  fof(f135,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | ~spl8_5),
% 1.31/0.54    inference(superposition,[],[f25,f130])).
% 1.31/0.54  fof(f130,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_5),
% 1.31/0.54    inference(forward_demodulation,[],[f129,f28])).
% 1.31/0.54  fof(f129,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_5),
% 1.31/0.54    inference(forward_demodulation,[],[f26,f55])).
% 1.31/0.54  fof(f55,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_5),
% 1.31/0.54    inference(avatar_component_clause,[],[f53])).
% 1.31/0.54  fof(f127,plain,(
% 1.31/0.54    ~spl8_8),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f126])).
% 1.31/0.54  fof(f126,plain,(
% 1.31/0.54    $false | ~spl8_8),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f122])).
% 1.31/0.54  fof(f122,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | ~spl8_8),
% 1.31/0.54    inference(superposition,[],[f25,f117])).
% 1.31/0.54  fof(f117,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_8),
% 1.31/0.54    inference(forward_demodulation,[],[f116,f28])).
% 1.31/0.54  fof(f116,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_8),
% 1.31/0.54    inference(forward_demodulation,[],[f113,f28])).
% 1.31/0.54  fof(f113,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK7) | ~spl8_8),
% 1.31/0.54    inference(backward_demodulation,[],[f26,f75])).
% 1.31/0.54  fof(f75,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_8),
% 1.31/0.54    inference(avatar_component_clause,[],[f73])).
% 1.31/0.54  fof(f111,plain,(
% 1.31/0.54    spl8_11 | spl8_12 | spl8_13 | ~spl8_7),
% 1.31/0.54    inference(avatar_split_clause,[],[f97,f61,f107,f103,f99])).
% 1.31/0.54  fof(f97,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_7),
% 1.31/0.54    inference(superposition,[],[f20,f63])).
% 1.31/0.54  fof(f95,plain,(
% 1.31/0.54    ~spl8_6),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f94])).
% 1.31/0.54  fof(f94,plain,(
% 1.31/0.54    $false | ~spl8_6),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f90])).
% 1.31/0.54  fof(f90,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | ~spl8_6),
% 1.31/0.54    inference(superposition,[],[f25,f88])).
% 1.31/0.54  fof(f88,plain,(
% 1.31/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_6),
% 1.31/0.54    inference(forward_demodulation,[],[f86,f27])).
% 1.31/0.54  fof(f86,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0) | ~spl8_6),
% 1.31/0.54    inference(backward_demodulation,[],[f26,f59])).
% 1.31/0.54  fof(f59,plain,(
% 1.31/0.54    k1_xboole_0 = sK7 | ~spl8_6),
% 1.31/0.54    inference(avatar_component_clause,[],[f57])).
% 1.31/0.54  fof(f64,plain,(
% 1.31/0.54    spl8_5 | spl8_6 | spl8_7),
% 1.31/0.54    inference(avatar_split_clause,[],[f51,f61,f57,f53])).
% 1.31/0.54  fof(f51,plain,(
% 1.31/0.54    k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 1.31/0.54    inference(superposition,[],[f20,f26])).
% 1.31/0.54  fof(f45,plain,(
% 1.31/0.54    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 1.31/0.54    inference(avatar_split_clause,[],[f16,f42,f38,f34,f30])).
% 1.31/0.54  fof(f16,plain,(
% 1.31/0.54    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 1.31/0.54    inference(cnf_transformation,[],[f11])).
% 1.31/0.54  % SZS output end Proof for theBenchmark
% 1.31/0.54  % (25745)------------------------------
% 1.31/0.54  % (25745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (25745)Termination reason: Refutation
% 1.31/0.54  
% 1.31/0.54  % (25745)Memory used [KB]: 6396
% 1.31/0.54  % (25745)Time elapsed: 0.108 s
% 1.31/0.54  % (25745)------------------------------
% 1.31/0.54  % (25745)------------------------------
% 1.31/0.54  % (25729)Success in time 0.179 s
%------------------------------------------------------------------------------
