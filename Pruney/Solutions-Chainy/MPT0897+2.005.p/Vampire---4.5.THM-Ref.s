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
% DateTime   : Thu Dec  3 12:59:14 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 266 expanded)
%              Number of leaves         :   19 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  300 ( 876 expanded)
%              Number of equality atoms :  181 ( 724 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f68,f83,f96,f100,f119,f137,f154,f161,f181,f186,f190,f209,f230])).

fof(f230,plain,
    ( spl8_2
    | ~ spl8_10
    | spl8_11
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl8_2
    | ~ spl8_10
    | spl8_11
    | spl8_12 ),
    inference(subsumption_resolution,[],[f228,f37])).

fof(f37,plain,
    ( sK1 != sK5
    | spl8_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl8_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f228,plain,
    ( sK1 = sK5
    | ~ spl8_10
    | spl8_11
    | spl8_12 ),
    inference(equality_resolution,[],[f203])).

fof(f203,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5)
        | sK5 = X5 )
    | ~ spl8_10
    | spl8_11
    | spl8_12 ),
    inference(subsumption_resolution,[],[f202,f172])).

fof(f172,plain,
    ( k1_xboole_0 != sK4
    | spl8_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f202,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = sK4
        | sK5 = X5 )
    | ~ spl8_10
    | spl8_12 ),
    inference(subsumption_resolution,[],[f197,f176])).

fof(f176,plain,
    ( k1_xboole_0 != sK5
    | spl8_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl8_12
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f197,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK5 = X5 )
    | ~ spl8_10 ),
    inference(superposition,[],[f19,f136])).

fof(f136,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_10
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f209,plain,
    ( spl8_1
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl8_1
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f207,f33])).

fof(f33,plain,
    ( sK0 != sK4
    | spl8_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl8_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f207,plain,
    ( sK0 = sK4
    | ~ spl8_13 ),
    inference(equality_resolution,[],[f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | sK4 = X0 )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl8_13
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | sK4 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f190,plain,
    ( spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f188,f113])).

fof(f113,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_8
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f188,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f187,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f187,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,k1_xboole_0)
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f136,f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f186,plain,
    ( spl8_8
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl8_8
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f184,f113])).

fof(f184,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f182,f29])).

fof(f29,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f182,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f136,f173])).

fof(f173,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f181,plain,
    ( spl8_11
    | spl8_12
    | spl8_13
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f162,f134,f179,f175,f171])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK4 = X0 )
    | ~ spl8_10 ),
    inference(superposition,[],[f18,f136])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f161,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f159,f29])).

fof(f159,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f158,f28])).

fof(f158,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f26,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f26,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f16,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f11])).

fof(f11,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f154,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f152,f29])).

fof(f152,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f142,f29])).

fof(f142,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f26,f114])).

fof(f114,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f137,plain,
    ( spl8_10
    | spl8_8
    | spl8_9
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f132,f80,f116,f112,f134])).

fof(f80,plain,
    ( spl8_7
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f132,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_7 ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k2_zfmisc_1(sK4,sK5) = X2 )
    | ~ spl8_7 ),
    inference(superposition,[],[f18,f82])).

fof(f82,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f119,plain,
    ( spl8_3
    | spl8_8
    | spl8_9
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f110,f80,f116,f112,f39])).

fof(f39,plain,
    ( spl8_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f110,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | sK2 = sK6
    | ~ spl8_7 ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k2_zfmisc_1(X6,X7)
        | k1_xboole_0 = X7
        | k1_xboole_0 = X6
        | sK6 = X7 )
    | ~ spl8_7 ),
    inference(superposition,[],[f19,f82])).

fof(f100,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f98,f28])).

fof(f98,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f26,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f96,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f86,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f26,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f83,plain,
    ( spl8_7
    | spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f59,f65,f61,f80])).

fof(f59,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0 ) ),
    inference(superposition,[],[f18,f27])).

fof(f27,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f15,f25,f25])).

fof(f15,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,
    ( spl8_4
    | spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f55,f65,f61,f43])).

fof(f43,plain,
    ( spl8_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f55,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | sK3 = sK7 ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X5] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X4,X5)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | sK7 = X5 ) ),
    inference(superposition,[],[f19,f27])).

fof(f46,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f17,f43,f39,f35,f31])).

fof(f17,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:50:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.47  % (27873)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.50  % (27894)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.51  % (27886)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.51  % (27880)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.52  % (27876)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  % (27881)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.52  % (27895)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.52  % (27883)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.52  % (27886)Refutation not found, incomplete strategy% (27886)------------------------------
% 0.23/0.52  % (27886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (27886)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (27886)Memory used [KB]: 10618
% 0.23/0.52  % (27886)Time elapsed: 0.114 s
% 0.23/0.52  % (27886)------------------------------
% 0.23/0.52  % (27886)------------------------------
% 0.23/0.53  % (27871)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.53  % (27887)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.53  % (27894)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f231,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(avatar_sat_refutation,[],[f46,f68,f83,f96,f100,f119,f137,f154,f161,f181,f186,f190,f209,f230])).
% 0.23/0.53  fof(f230,plain,(
% 0.23/0.53    spl8_2 | ~spl8_10 | spl8_11 | spl8_12),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f229])).
% 0.23/0.53  fof(f229,plain,(
% 0.23/0.53    $false | (spl8_2 | ~spl8_10 | spl8_11 | spl8_12)),
% 0.23/0.53    inference(subsumption_resolution,[],[f228,f37])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    sK1 != sK5 | spl8_2),
% 0.23/0.53    inference(avatar_component_clause,[],[f35])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    spl8_2 <=> sK1 = sK5),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.23/0.53  fof(f228,plain,(
% 0.23/0.53    sK1 = sK5 | (~spl8_10 | spl8_11 | spl8_12)),
% 0.23/0.53    inference(equality_resolution,[],[f203])).
% 0.23/0.53  fof(f203,plain,(
% 0.23/0.53    ( ! [X4,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5) | sK5 = X5) ) | (~spl8_10 | spl8_11 | spl8_12)),
% 0.23/0.53    inference(subsumption_resolution,[],[f202,f172])).
% 0.23/0.53  fof(f172,plain,(
% 0.23/0.53    k1_xboole_0 != sK4 | spl8_11),
% 0.23/0.53    inference(avatar_component_clause,[],[f171])).
% 0.23/0.53  fof(f171,plain,(
% 0.23/0.53    spl8_11 <=> k1_xboole_0 = sK4),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.23/0.53  fof(f202,plain,(
% 0.23/0.53    ( ! [X4,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = sK4 | sK5 = X5) ) | (~spl8_10 | spl8_12)),
% 0.23/0.53    inference(subsumption_resolution,[],[f197,f176])).
% 0.23/0.53  fof(f176,plain,(
% 0.23/0.53    k1_xboole_0 != sK5 | spl8_12),
% 0.23/0.53    inference(avatar_component_clause,[],[f175])).
% 0.23/0.53  fof(f175,plain,(
% 0.23/0.53    spl8_12 <=> k1_xboole_0 = sK5),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.23/0.53  fof(f197,plain,(
% 0.23/0.53    ( ! [X4,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK5 = X5) ) | ~spl8_10),
% 0.23/0.53    inference(superposition,[],[f19,f136])).
% 0.23/0.53  fof(f136,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_10),
% 0.23/0.53    inference(avatar_component_clause,[],[f134])).
% 0.23/0.53  fof(f134,plain,(
% 0.23/0.53    spl8_10 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.23/0.53    inference(flattening,[],[f9])).
% 0.23/0.53  fof(f9,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.23/0.53  fof(f209,plain,(
% 0.23/0.53    spl8_1 | ~spl8_13),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f208])).
% 0.23/0.53  fof(f208,plain,(
% 0.23/0.53    $false | (spl8_1 | ~spl8_13)),
% 0.23/0.53    inference(subsumption_resolution,[],[f207,f33])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    sK0 != sK4 | spl8_1),
% 0.23/0.53    inference(avatar_component_clause,[],[f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    spl8_1 <=> sK0 = sK4),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.23/0.53  fof(f207,plain,(
% 0.23/0.53    sK0 = sK4 | ~spl8_13),
% 0.23/0.53    inference(equality_resolution,[],[f180])).
% 0.23/0.53  fof(f180,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | sK4 = X0) ) | ~spl8_13),
% 0.23/0.53    inference(avatar_component_clause,[],[f179])).
% 0.23/0.53  fof(f179,plain,(
% 0.23/0.53    spl8_13 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | sK4 = X0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.23/0.53  fof(f190,plain,(
% 0.23/0.53    spl8_8 | ~spl8_10 | ~spl8_12),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f189])).
% 0.23/0.53  fof(f189,plain,(
% 0.23/0.53    $false | (spl8_8 | ~spl8_10 | ~spl8_12)),
% 0.23/0.53    inference(subsumption_resolution,[],[f188,f113])).
% 0.23/0.53  fof(f113,plain,(
% 0.23/0.53    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl8_8),
% 0.23/0.53    inference(avatar_component_clause,[],[f112])).
% 0.23/0.53  fof(f112,plain,(
% 0.23/0.53    spl8_8 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.23/0.53  fof(f188,plain,(
% 0.23/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl8_10 | ~spl8_12)),
% 0.23/0.53    inference(forward_demodulation,[],[f187,f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.53    inference(equality_resolution,[],[f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.23/0.53    inference(flattening,[],[f13])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.23/0.53    inference(nnf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.53  fof(f187,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,k1_xboole_0) | (~spl8_10 | ~spl8_12)),
% 0.23/0.53    inference(forward_demodulation,[],[f136,f177])).
% 0.23/0.53  fof(f177,plain,(
% 0.23/0.53    k1_xboole_0 = sK5 | ~spl8_12),
% 0.23/0.53    inference(avatar_component_clause,[],[f175])).
% 0.23/0.53  fof(f186,plain,(
% 0.23/0.53    spl8_8 | ~spl8_10 | ~spl8_11),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f185])).
% 0.23/0.53  fof(f185,plain,(
% 0.23/0.53    $false | (spl8_8 | ~spl8_10 | ~spl8_11)),
% 0.23/0.53    inference(subsumption_resolution,[],[f184,f113])).
% 0.23/0.53  fof(f184,plain,(
% 0.23/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl8_10 | ~spl8_11)),
% 0.23/0.53    inference(forward_demodulation,[],[f182,f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.23/0.53    inference(equality_resolution,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f182,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK5) | (~spl8_10 | ~spl8_11)),
% 0.23/0.53    inference(backward_demodulation,[],[f136,f173])).
% 0.23/0.53  fof(f173,plain,(
% 0.23/0.53    k1_xboole_0 = sK4 | ~spl8_11),
% 0.23/0.53    inference(avatar_component_clause,[],[f171])).
% 0.23/0.53  fof(f181,plain,(
% 0.23/0.53    spl8_11 | spl8_12 | spl8_13 | ~spl8_10),
% 0.23/0.53    inference(avatar_split_clause,[],[f162,f134,f179,f175,f171])).
% 0.23/0.53  fof(f162,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK4 = X0) ) | ~spl8_10),
% 0.23/0.53    inference(superposition,[],[f18,f136])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X2) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f161,plain,(
% 0.23/0.53    ~spl8_9),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f160])).
% 0.23/0.53  fof(f160,plain,(
% 0.23/0.53    $false | ~spl8_9),
% 0.23/0.53    inference(subsumption_resolution,[],[f159,f29])).
% 0.23/0.53  fof(f159,plain,(
% 0.23/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | ~spl8_9),
% 0.23/0.53    inference(forward_demodulation,[],[f158,f28])).
% 0.23/0.53  fof(f158,plain,(
% 0.23/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3) | ~spl8_9),
% 0.23/0.53    inference(forward_demodulation,[],[f26,f118])).
% 0.23/0.53  fof(f118,plain,(
% 0.23/0.53    k1_xboole_0 = sK2 | ~spl8_9),
% 0.23/0.53    inference(avatar_component_clause,[],[f116])).
% 0.23/0.53  fof(f116,plain,(
% 0.23/0.53    spl8_9 <=> k1_xboole_0 = sK2),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.23/0.53    inference(definition_unfolding,[],[f16,f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f23,f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f11])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f8,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.23/0.53    inference(flattening,[],[f7])).
% 0.23/0.53  fof(f7,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.23/0.53    inference(ennf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.23/0.53    inference(negated_conjecture,[],[f5])).
% 0.23/0.53  fof(f5,conjecture,(
% 0.23/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).
% 0.23/0.53  fof(f154,plain,(
% 0.23/0.53    ~spl8_8),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f153])).
% 0.23/0.53  fof(f153,plain,(
% 0.23/0.53    $false | ~spl8_8),
% 0.23/0.53    inference(subsumption_resolution,[],[f152,f29])).
% 0.23/0.53  fof(f152,plain,(
% 0.23/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | ~spl8_8),
% 0.23/0.53    inference(forward_demodulation,[],[f142,f29])).
% 0.23/0.53  fof(f142,plain,(
% 0.23/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | ~spl8_8),
% 0.23/0.53    inference(backward_demodulation,[],[f26,f114])).
% 0.23/0.53  fof(f114,plain,(
% 0.23/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_8),
% 0.23/0.53    inference(avatar_component_clause,[],[f112])).
% 0.23/0.53  fof(f137,plain,(
% 0.23/0.53    spl8_10 | spl8_8 | spl8_9 | ~spl8_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f132,f80,f116,f112,f134])).
% 0.23/0.53  fof(f80,plain,(
% 0.23/0.53    spl8_7 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.23/0.53  fof(f132,plain,(
% 0.23/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_7),
% 0.23/0.53    inference(equality_resolution,[],[f102])).
% 0.23/0.53  fof(f102,plain,(
% 0.23/0.53    ( ! [X2,X3] : (k2_zfmisc_1(X2,X3) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k2_zfmisc_1(sK4,sK5) = X2) ) | ~spl8_7),
% 0.23/0.53    inference(superposition,[],[f18,f82])).
% 0.23/0.53  fof(f82,plain,(
% 0.23/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_7),
% 0.23/0.53    inference(avatar_component_clause,[],[f80])).
% 0.23/0.53  fof(f119,plain,(
% 0.23/0.53    spl8_3 | spl8_8 | spl8_9 | ~spl8_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f110,f80,f116,f112,f39])).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    spl8_3 <=> sK2 = sK6),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.23/0.53  fof(f110,plain,(
% 0.23/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | sK2 = sK6 | ~spl8_7),
% 0.23/0.53    inference(equality_resolution,[],[f104])).
% 0.23/0.53  fof(f104,plain,(
% 0.23/0.53    ( ! [X6,X7] : (k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k2_zfmisc_1(X6,X7) | k1_xboole_0 = X7 | k1_xboole_0 = X6 | sK6 = X7) ) | ~spl8_7),
% 0.23/0.53    inference(superposition,[],[f19,f82])).
% 0.23/0.53  fof(f100,plain,(
% 0.23/0.53    ~spl8_6),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f99])).
% 0.23/0.53  fof(f99,plain,(
% 0.23/0.53    $false | ~spl8_6),
% 0.23/0.53    inference(subsumption_resolution,[],[f98,f28])).
% 0.23/0.53  fof(f98,plain,(
% 0.23/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | ~spl8_6),
% 0.23/0.53    inference(forward_demodulation,[],[f26,f67])).
% 0.23/0.53  fof(f67,plain,(
% 0.23/0.53    k1_xboole_0 = sK3 | ~spl8_6),
% 0.23/0.53    inference(avatar_component_clause,[],[f65])).
% 0.23/0.53  fof(f65,plain,(
% 0.23/0.53    spl8_6 <=> k1_xboole_0 = sK3),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.23/0.53  fof(f96,plain,(
% 0.23/0.53    ~spl8_5),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f95])).
% 0.23/0.53  fof(f95,plain,(
% 0.23/0.53    $false | ~spl8_5),
% 0.23/0.53    inference(subsumption_resolution,[],[f86,f29])).
% 0.23/0.53  fof(f86,plain,(
% 0.23/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | ~spl8_5),
% 0.23/0.53    inference(backward_demodulation,[],[f26,f63])).
% 0.23/0.53  fof(f63,plain,(
% 0.23/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_5),
% 0.23/0.53    inference(avatar_component_clause,[],[f61])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.23/0.53  fof(f83,plain,(
% 0.23/0.53    spl8_7 | spl8_5 | spl8_6),
% 0.23/0.53    inference(avatar_split_clause,[],[f59,f65,f61,f80])).
% 0.23/0.53  fof(f59,plain,(
% 0.23/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 0.23/0.53    inference(equality_resolution,[],[f48])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0) )),
% 0.23/0.53    inference(superposition,[],[f18,f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.23/0.53    inference(definition_unfolding,[],[f15,f25,f25])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f68,plain,(
% 0.23/0.53    spl8_4 | spl8_5 | spl8_6),
% 0.23/0.53    inference(avatar_split_clause,[],[f55,f65,f61,f43])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    spl8_4 <=> sK3 = sK7),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | sK3 = sK7),
% 0.23/0.53    inference(equality_resolution,[],[f50])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    ( ! [X4,X5] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | sK7 = X5) )),
% 0.23/0.53    inference(superposition,[],[f19,f27])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.23/0.53    inference(avatar_split_clause,[],[f17,f43,f39,f35,f31])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (27894)------------------------------
% 0.23/0.53  % (27894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (27894)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (27894)Memory used [KB]: 10746
% 0.23/0.53  % (27894)Time elapsed: 0.128 s
% 0.23/0.53  % (27894)------------------------------
% 0.23/0.53  % (27894)------------------------------
% 0.23/0.53  % (27869)Success in time 0.157 s
%------------------------------------------------------------------------------
