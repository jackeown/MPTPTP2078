%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 332 expanded)
%              Number of leaves         :   21 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  477 (1212 expanded)
%              Number of equality atoms :  300 ( 978 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f519,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f82,f86,f90,f106,f111,f114,f175,f194,f213,f286,f323,f374,f513,f518])).

fof(f518,plain,
    ( spl8_4
    | spl8_6
    | spl8_8
    | spl8_9
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | spl8_4
    | spl8_6
    | spl8_8
    | spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f128,f62])).

fof(f62,plain,
    ( sK3 != sK7
    | spl8_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f128,plain,
    ( sK3 = sK7
    | spl8_6
    | spl8_8
    | spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f127,f95])).

fof(f95,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_8
  <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f127,plain,
    ( sK3 = sK7
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | spl8_6
    | spl8_8
    | spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f125,f99])).

fof(f99,plain,
    ( k1_xboole_0 != sK3
    | spl8_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f125,plain,
    ( sK3 = sK7
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | spl8_6
    | spl8_8
    | ~ spl8_10 ),
    inference(superposition,[],[f124,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f124,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | spl8_6
    | spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f123,f95])).

fof(f123,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f122,f76])).

fof(f76,plain,
    ( k1_xboole_0 != sK7
    | spl8_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f122,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_10 ),
    inference(superposition,[],[f26,f117])).

fof(f117,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7)
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f37,f104])).

fof(f104,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_10
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f37,plain,(
    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    inference(definition_unfolding,[],[f19,f31,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f19,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f13])).

% (1859)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f13,plain,
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

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f513,plain,
    ( spl8_1
    | spl8_15
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f430,f158,f154,f150,f102,f284,f48])).

fof(f48,plain,
    ( spl8_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f284,plain,
    ( spl8_15
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f150,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f154,plain,
    ( spl8_12
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f158,plain,
    ( spl8_13
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f430,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK0 = sK4 )
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(equality_resolution,[],[f251])).

fof(f251,plain,
    ( ! [X30,X33,X31,X34,X32] :
        ( k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X30)
        | k1_xboole_0 = X30
        | sK4 = X31 )
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(subsumption_resolution,[],[f250,f151])).

fof(f151,plain,
    ( k1_xboole_0 != sK4
    | spl8_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f250,plain,
    ( ! [X30,X33,X31,X34,X32] :
        ( k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X30)
        | k1_xboole_0 = X30
        | k1_xboole_0 = sK4
        | sK4 = X31 )
    | ~ spl8_10
    | spl8_12
    | spl8_13 ),
    inference(subsumption_resolution,[],[f249,f155])).

fof(f155,plain,
    ( k1_xboole_0 != sK5
    | spl8_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f249,plain,
    ( ! [X30,X33,X31,X34,X32] :
        ( k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X30)
        | k1_xboole_0 = X30
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK4 = X31 )
    | ~ spl8_10
    | spl8_13 ),
    inference(subsumption_resolution,[],[f238,f159])).

fof(f159,plain,
    ( k1_xboole_0 != sK6
    | spl8_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f238,plain,
    ( ! [X30,X33,X31,X34,X32] :
        ( k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X30)
        | k1_xboole_0 = X30
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK4 = X31 )
    | ~ spl8_10 ),
    inference(superposition,[],[f41,f104])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X4 ) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f374,plain,(
    ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f335,f43])).

fof(f43,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f335,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_15 ),
    inference(backward_demodulation,[],[f36,f285])).

fof(f285,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f284])).

fof(f36,plain,(
    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f20,f31])).

fof(f20,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f323,plain,
    ( spl8_2
    | spl8_15
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f318,f158,f154,f150,f102,f284,f52])).

fof(f52,plain,
    ( spl8_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f318,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK1 = sK5 )
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(equality_resolution,[],[f248])).

fof(f248,plain,
    ( ! [X24,X23,X21,X22,X20] :
        ( k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X20)
        | k1_xboole_0 = X20
        | sK5 = X22 )
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(subsumption_resolution,[],[f247,f151])).

fof(f247,plain,
    ( ! [X24,X23,X21,X22,X20] :
        ( k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X20)
        | k1_xboole_0 = X20
        | k1_xboole_0 = sK4
        | sK5 = X22 )
    | ~ spl8_10
    | spl8_12
    | spl8_13 ),
    inference(subsumption_resolution,[],[f246,f155])).

fof(f246,plain,
    ( ! [X24,X23,X21,X22,X20] :
        ( k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X20)
        | k1_xboole_0 = X20
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK5 = X22 )
    | ~ spl8_10
    | spl8_13 ),
    inference(subsumption_resolution,[],[f236,f159])).

fof(f236,plain,
    ( ! [X24,X23,X21,X22,X20] :
        ( k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X20)
        | k1_xboole_0 = X20
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK5 = X22 )
    | ~ spl8_10 ),
    inference(superposition,[],[f40,f104])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X5 ) ),
    inference(definition_unfolding,[],[f33,f31,f31])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X1 = X5
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f286,plain,
    ( spl8_3
    | spl8_15
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f278,f158,f154,f150,f102,f284,f56])).

fof(f56,plain,
    ( spl8_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f278,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK2 = sK6 )
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(equality_resolution,[],[f245])).

% (1870)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f245,plain,
    ( ! [X14,X12,X10,X13,X11] :
        ( k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X10)
        | k1_xboole_0 = X10
        | sK6 = X13 )
    | ~ spl8_10
    | spl8_11
    | spl8_12
    | spl8_13 ),
    inference(subsumption_resolution,[],[f244,f151])).

fof(f244,plain,
    ( ! [X14,X12,X10,X13,X11] :
        ( k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X10)
        | k1_xboole_0 = X10
        | k1_xboole_0 = sK4
        | sK6 = X13 )
    | ~ spl8_10
    | spl8_12
    | spl8_13 ),
    inference(subsumption_resolution,[],[f243,f155])).

fof(f243,plain,
    ( ! [X14,X12,X10,X13,X11] :
        ( k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X10)
        | k1_xboole_0 = X10
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK6 = X13 )
    | ~ spl8_10
    | spl8_13 ),
    inference(subsumption_resolution,[],[f234,f159])).

fof(f234,plain,
    ( ! [X14,X12,X10,X13,X11] :
        ( k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X10)
        | k1_xboole_0 = X10
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK6 = X13 )
    | ~ spl8_10 ),
    inference(superposition,[],[f39,f104])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X6 ) ),
    inference(definition_unfolding,[],[f34,f31,f31])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X2 = X6
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f213,plain,
    ( spl8_5
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl8_5
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f211,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f211,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK4,sK5,k1_xboole_0)
    | spl8_5
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f72,f160])).

fof(f160,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f72,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK4,sK5,sK6)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_5
  <=> k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f194,plain,
    ( spl8_5
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl8_5
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f192,f45])).

fof(f45,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f192,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK4,k1_xboole_0,sK6)
    | spl8_5
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f72,f156])).

fof(f156,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f175,plain,
    ( spl8_5
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl8_5
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f169,f46])).

fof(f46,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f169,plain,
    ( k1_xboole_0 != k3_zfmisc_1(k1_xboole_0,sK5,sK6)
    | spl8_5
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f72,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f114,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f112,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f36,f100])).

fof(f100,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f98])).

% (1863)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f111,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f108,f43])).

fof(f108,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f36,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f106,plain,
    ( spl8_8
    | spl8_9
    | spl8_10
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f92,f79,f102,f98,f94])).

fof(f79,plain,
    ( spl8_7
  <=> k3_zfmisc_1(sK4,sK5,sK6) = k1_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f92,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_7 ),
    inference(superposition,[],[f25,f81])).

fof(f81,plain,
    ( k3_zfmisc_1(sK4,sK5,sK6) = k1_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f88,f36])).

fof(f88,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f87,f42])).

fof(f87,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f37,f77])).

fof(f77,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f86,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f84,f36])).

fof(f84,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f83,f43])).

fof(f83,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f37,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f82,plain,
    ( spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f69,f79,f75,f71])).

fof(f69,plain,
    ( k3_zfmisc_1(sK4,sK5,sK6) = k1_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) ),
    inference(superposition,[],[f25,f37])).

fof(f63,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f21,f60,f56,f52,f48])).

fof(f21,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n003.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 10:29:57 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.46  % (1864)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (1880)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.49  % (1872)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.49  % (1868)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.49  % (1862)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.49  % (1881)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.49  % (1873)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.49  % (1858)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.50  % (1867)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.50  % (1864)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (1860)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.50  % (1871)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f519,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f63,f82,f86,f90,f106,f111,f114,f175,f194,f213,f286,f323,f374,f513,f518])).
% 0.19/0.50  fof(f518,plain,(
% 0.19/0.50    spl8_4 | spl8_6 | spl8_8 | spl8_9 | ~spl8_10),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f517])).
% 0.19/0.50  fof(f517,plain,(
% 0.19/0.50    $false | (spl8_4 | spl8_6 | spl8_8 | spl8_9 | ~spl8_10)),
% 0.19/0.50    inference(subsumption_resolution,[],[f128,f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    sK3 != sK7 | spl8_4),
% 0.19/0.50    inference(avatar_component_clause,[],[f60])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    spl8_4 <=> sK3 = sK7),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.19/0.50  fof(f128,plain,(
% 0.19/0.50    sK3 = sK7 | (spl8_6 | spl8_8 | spl8_9 | ~spl8_10)),
% 0.19/0.50    inference(subsumption_resolution,[],[f127,f95])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) | spl8_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f94])).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    spl8_8 <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.19/0.50  fof(f127,plain,(
% 0.19/0.50    sK3 = sK7 | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | (spl8_6 | spl8_8 | spl8_9 | ~spl8_10)),
% 0.19/0.50    inference(subsumption_resolution,[],[f125,f99])).
% 0.19/0.50  fof(f99,plain,(
% 0.19/0.50    k1_xboole_0 != sK3 | spl8_9),
% 0.19/0.50    inference(avatar_component_clause,[],[f98])).
% 0.19/0.50  fof(f98,plain,(
% 0.19/0.50    spl8_9 <=> k1_xboole_0 = sK3),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.19/0.50  fof(f125,plain,(
% 0.19/0.50    sK3 = sK7 | k1_xboole_0 = sK3 | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | (spl8_6 | spl8_8 | ~spl8_10)),
% 0.19/0.50    inference(superposition,[],[f124,f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.19/0.50  fof(f124,plain,(
% 0.19/0.50    sK7 = k2_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | (spl8_6 | spl8_8 | ~spl8_10)),
% 0.19/0.50    inference(subsumption_resolution,[],[f123,f95])).
% 0.19/0.50  fof(f123,plain,(
% 0.19/0.50    sK7 = k2_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | (spl8_6 | ~spl8_10)),
% 0.19/0.50    inference(subsumption_resolution,[],[f122,f76])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    k1_xboole_0 != sK7 | spl8_6),
% 0.19/0.50    inference(avatar_component_clause,[],[f75])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    spl8_6 <=> k1_xboole_0 = sK7),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.19/0.50  fof(f122,plain,(
% 0.19/0.50    sK7 = k2_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK7 | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | ~spl8_10),
% 0.19/0.50    inference(superposition,[],[f26,f117])).
% 0.19/0.50  fof(f117,plain,(
% 0.19/0.50    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK7) | ~spl8_10),
% 0.19/0.50    inference(forward_demodulation,[],[f37,f104])).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6) | ~spl8_10),
% 0.19/0.50    inference(avatar_component_clause,[],[f102])).
% 0.19/0.50  fof(f102,plain,(
% 0.19/0.50    spl8_10 <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)),
% 0.19/0.50    inference(definition_unfolding,[],[f19,f31,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f13])).
% 0.19/0.50  % (1859)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f9,plain,(
% 0.19/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.19/0.50    inference(flattening,[],[f8])).
% 0.19/0.50  fof(f8,plain,(
% 0.19/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.19/0.50    inference(negated_conjecture,[],[f6])).
% 0.19/0.50  fof(f6,conjecture,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).
% 0.19/0.50  fof(f513,plain,(
% 0.19/0.50    spl8_1 | spl8_15 | ~spl8_10 | spl8_11 | spl8_12 | spl8_13),
% 0.19/0.50    inference(avatar_split_clause,[],[f430,f158,f154,f150,f102,f284,f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    spl8_1 <=> sK0 = sK4),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.19/0.50  fof(f284,plain,(
% 0.19/0.50    spl8_15 <=> ! [X0] : k1_xboole_0 = X0),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.19/0.50  fof(f150,plain,(
% 0.19/0.50    spl8_11 <=> k1_xboole_0 = sK4),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.19/0.50  fof(f154,plain,(
% 0.19/0.50    spl8_12 <=> k1_xboole_0 = sK5),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.19/0.50  fof(f158,plain,(
% 0.19/0.50    spl8_13 <=> k1_xboole_0 = sK6),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.19/0.50  fof(f430,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = X0 | sK0 = sK4) ) | (~spl8_10 | spl8_11 | spl8_12 | spl8_13)),
% 0.19/0.50    inference(equality_resolution,[],[f251])).
% 0.19/0.50  fof(f251,plain,(
% 0.19/0.50    ( ! [X30,X33,X31,X34,X32] : (k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X30) | k1_xboole_0 = X30 | sK4 = X31) ) | (~spl8_10 | spl8_11 | spl8_12 | spl8_13)),
% 0.19/0.50    inference(subsumption_resolution,[],[f250,f151])).
% 0.19/0.50  fof(f151,plain,(
% 0.19/0.50    k1_xboole_0 != sK4 | spl8_11),
% 0.19/0.50    inference(avatar_component_clause,[],[f150])).
% 0.19/0.50  fof(f250,plain,(
% 0.19/0.50    ( ! [X30,X33,X31,X34,X32] : (k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X30) | k1_xboole_0 = X30 | k1_xboole_0 = sK4 | sK4 = X31) ) | (~spl8_10 | spl8_12 | spl8_13)),
% 0.19/0.50    inference(subsumption_resolution,[],[f249,f155])).
% 0.19/0.50  fof(f155,plain,(
% 0.19/0.50    k1_xboole_0 != sK5 | spl8_12),
% 0.19/0.50    inference(avatar_component_clause,[],[f154])).
% 0.19/0.50  fof(f249,plain,(
% 0.19/0.50    ( ! [X30,X33,X31,X34,X32] : (k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X30) | k1_xboole_0 = X30 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK4 = X31) ) | (~spl8_10 | spl8_13)),
% 0.19/0.50    inference(subsumption_resolution,[],[f238,f159])).
% 0.19/0.50  fof(f159,plain,(
% 0.19/0.50    k1_xboole_0 != sK6 | spl8_13),
% 0.19/0.50    inference(avatar_component_clause,[],[f158])).
% 0.19/0.50  fof(f238,plain,(
% 0.19/0.50    ( ! [X30,X33,X31,X34,X32] : (k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X30) | k1_xboole_0 = X30 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK4 = X31) ) | ~spl8_10),
% 0.19/0.50    inference(superposition,[],[f41,f104])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X4) )),
% 0.19/0.50    inference(definition_unfolding,[],[f32,f31,f31])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X0 = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.19/0.50    inference(flattening,[],[f11])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.19/0.50  fof(f374,plain,(
% 0.19/0.50    ~spl8_15),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f373])).
% 0.19/0.50  fof(f373,plain,(
% 0.19/0.50    $false | ~spl8_15),
% 0.19/0.50    inference(subsumption_resolution,[],[f335,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.50    inference(equality_resolution,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.51    inference(flattening,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.51    inference(nnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.51  fof(f335,plain,(
% 0.19/0.51    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | ~spl8_15),
% 0.19/0.51    inference(backward_demodulation,[],[f36,f285])).
% 0.19/0.51  fof(f285,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl8_15),
% 0.19/0.51    inference(avatar_component_clause,[],[f284])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)),
% 0.19/0.51    inference(definition_unfolding,[],[f20,f31])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f323,plain,(
% 0.19/0.51    spl8_2 | spl8_15 | ~spl8_10 | spl8_11 | spl8_12 | spl8_13),
% 0.19/0.51    inference(avatar_split_clause,[],[f318,f158,f154,f150,f102,f284,f52])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    spl8_2 <=> sK1 = sK5),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.19/0.51  fof(f318,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = X0 | sK1 = sK5) ) | (~spl8_10 | spl8_11 | spl8_12 | spl8_13)),
% 0.19/0.51    inference(equality_resolution,[],[f248])).
% 0.19/0.51  fof(f248,plain,(
% 0.19/0.51    ( ! [X24,X23,X21,X22,X20] : (k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X20) | k1_xboole_0 = X20 | sK5 = X22) ) | (~spl8_10 | spl8_11 | spl8_12 | spl8_13)),
% 0.19/0.51    inference(subsumption_resolution,[],[f247,f151])).
% 0.19/0.51  fof(f247,plain,(
% 0.19/0.51    ( ! [X24,X23,X21,X22,X20] : (k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X20) | k1_xboole_0 = X20 | k1_xboole_0 = sK4 | sK5 = X22) ) | (~spl8_10 | spl8_12 | spl8_13)),
% 0.19/0.51    inference(subsumption_resolution,[],[f246,f155])).
% 0.19/0.51  fof(f246,plain,(
% 0.19/0.51    ( ! [X24,X23,X21,X22,X20] : (k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X20) | k1_xboole_0 = X20 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK5 = X22) ) | (~spl8_10 | spl8_13)),
% 0.19/0.51    inference(subsumption_resolution,[],[f236,f159])).
% 0.19/0.51  fof(f236,plain,(
% 0.19/0.51    ( ! [X24,X23,X21,X22,X20] : (k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X20) | k1_xboole_0 = X20 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK5 = X22) ) | ~spl8_10),
% 0.19/0.51    inference(superposition,[],[f40,f104])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X5) )),
% 0.19/0.51    inference(definition_unfolding,[],[f33,f31,f31])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X1 = X5 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f12])).
% 0.19/0.51  fof(f286,plain,(
% 0.19/0.51    spl8_3 | spl8_15 | ~spl8_10 | spl8_11 | spl8_12 | spl8_13),
% 0.19/0.51    inference(avatar_split_clause,[],[f278,f158,f154,f150,f102,f284,f56])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    spl8_3 <=> sK2 = sK6),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.19/0.51  fof(f278,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = X0 | sK2 = sK6) ) | (~spl8_10 | spl8_11 | spl8_12 | spl8_13)),
% 0.19/0.51    inference(equality_resolution,[],[f245])).
% 0.19/0.51  % (1870)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.51  fof(f245,plain,(
% 0.19/0.51    ( ! [X14,X12,X10,X13,X11] : (k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X10) | k1_xboole_0 = X10 | sK6 = X13) ) | (~spl8_10 | spl8_11 | spl8_12 | spl8_13)),
% 0.19/0.51    inference(subsumption_resolution,[],[f244,f151])).
% 0.19/0.51  fof(f244,plain,(
% 0.19/0.51    ( ! [X14,X12,X10,X13,X11] : (k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X10) | k1_xboole_0 = X10 | k1_xboole_0 = sK4 | sK6 = X13) ) | (~spl8_10 | spl8_12 | spl8_13)),
% 0.19/0.51    inference(subsumption_resolution,[],[f243,f155])).
% 0.19/0.51  fof(f243,plain,(
% 0.19/0.51    ( ! [X14,X12,X10,X13,X11] : (k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X10) | k1_xboole_0 = X10 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK6 = X13) ) | (~spl8_10 | spl8_13)),
% 0.19/0.51    inference(subsumption_resolution,[],[f234,f159])).
% 0.19/0.51  fof(f234,plain,(
% 0.19/0.51    ( ! [X14,X12,X10,X13,X11] : (k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),X10) | k1_xboole_0 = X10 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK6 = X13) ) | ~spl8_10),
% 0.19/0.51    inference(superposition,[],[f39,f104])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X2 = X6) )),
% 0.19/0.51    inference(definition_unfolding,[],[f34,f31,f31])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X2 = X6 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f12])).
% 0.19/0.51  fof(f213,plain,(
% 0.19/0.51    spl8_5 | ~spl8_13),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f212])).
% 0.19/0.51  fof(f212,plain,(
% 0.19/0.51    $false | (spl8_5 | ~spl8_13)),
% 0.19/0.51    inference(subsumption_resolution,[],[f211,f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.51    inference(flattening,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.51    inference(nnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.19/0.51  fof(f211,plain,(
% 0.19/0.51    k1_xboole_0 != k3_zfmisc_1(sK4,sK5,k1_xboole_0) | (spl8_5 | ~spl8_13)),
% 0.19/0.51    inference(forward_demodulation,[],[f72,f160])).
% 0.19/0.51  fof(f160,plain,(
% 0.19/0.51    k1_xboole_0 = sK6 | ~spl8_13),
% 0.19/0.51    inference(avatar_component_clause,[],[f158])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    k1_xboole_0 != k3_zfmisc_1(sK4,sK5,sK6) | spl8_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    spl8_5 <=> k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.19/0.51  fof(f194,plain,(
% 0.19/0.51    spl8_5 | ~spl8_12),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f193])).
% 0.19/0.51  fof(f193,plain,(
% 0.19/0.51    $false | (spl8_5 | ~spl8_12)),
% 0.19/0.51    inference(subsumption_resolution,[],[f192,f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X2,X0] : (k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2)) )),
% 0.19/0.51    inference(equality_resolution,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f192,plain,(
% 0.19/0.51    k1_xboole_0 != k3_zfmisc_1(sK4,k1_xboole_0,sK6) | (spl8_5 | ~spl8_12)),
% 0.19/0.51    inference(forward_demodulation,[],[f72,f156])).
% 0.19/0.51  fof(f156,plain,(
% 0.19/0.51    k1_xboole_0 = sK5 | ~spl8_12),
% 0.19/0.51    inference(avatar_component_clause,[],[f154])).
% 0.19/0.51  fof(f175,plain,(
% 0.19/0.51    spl8_5 | ~spl8_11),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f174])).
% 0.19/0.51  fof(f174,plain,(
% 0.19/0.51    $false | (spl8_5 | ~spl8_11)),
% 0.19/0.51    inference(subsumption_resolution,[],[f169,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X2,X1] : (k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2)) )),
% 0.19/0.51    inference(equality_resolution,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f169,plain,(
% 0.19/0.51    k1_xboole_0 != k3_zfmisc_1(k1_xboole_0,sK5,sK6) | (spl8_5 | ~spl8_11)),
% 0.19/0.51    inference(backward_demodulation,[],[f72,f152])).
% 0.19/0.51  fof(f152,plain,(
% 0.19/0.51    k1_xboole_0 = sK4 | ~spl8_11),
% 0.19/0.51    inference(avatar_component_clause,[],[f150])).
% 0.19/0.51  fof(f114,plain,(
% 0.19/0.51    ~spl8_9),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f113])).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    $false | ~spl8_9),
% 0.19/0.51    inference(subsumption_resolution,[],[f112,f42])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) | ~spl8_9),
% 0.19/0.51    inference(backward_demodulation,[],[f36,f100])).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    k1_xboole_0 = sK3 | ~spl8_9),
% 0.19/0.51    inference(avatar_component_clause,[],[f98])).
% 0.19/0.51  % (1863)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  fof(f111,plain,(
% 0.19/0.51    ~spl8_8),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f110])).
% 0.19/0.51  fof(f110,plain,(
% 0.19/0.51    $false | ~spl8_8),
% 0.19/0.51    inference(subsumption_resolution,[],[f108,f43])).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | ~spl8_8),
% 0.19/0.51    inference(backward_demodulation,[],[f36,f96])).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | ~spl8_8),
% 0.19/0.51    inference(avatar_component_clause,[],[f94])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    spl8_8 | spl8_9 | spl8_10 | ~spl8_7),
% 0.19/0.51    inference(avatar_split_clause,[],[f92,f79,f102,f98,f94])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    spl8_7 <=> k3_zfmisc_1(sK4,sK5,sK6) = k1_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | ~spl8_7),
% 0.19/0.51    inference(superposition,[],[f25,f81])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    k3_zfmisc_1(sK4,sK5,sK6) = k1_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | ~spl8_7),
% 0.19/0.51    inference(avatar_component_clause,[],[f79])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f10])).
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    ~spl8_6),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f89])).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    $false | ~spl8_6),
% 0.19/0.51    inference(subsumption_resolution,[],[f88,f36])).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | ~spl8_6),
% 0.19/0.51    inference(forward_demodulation,[],[f87,f42])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),k1_xboole_0) | ~spl8_6),
% 0.19/0.51    inference(forward_demodulation,[],[f37,f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    k1_xboole_0 = sK7 | ~spl8_6),
% 0.19/0.51    inference(avatar_component_clause,[],[f75])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    ~spl8_5),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f85])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    $false | ~spl8_5),
% 0.19/0.51    inference(subsumption_resolution,[],[f84,f36])).
% 0.19/0.51  fof(f84,plain,(
% 0.19/0.51    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | ~spl8_5),
% 0.19/0.51    inference(forward_demodulation,[],[f83,f43])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_5),
% 0.19/0.51    inference(backward_demodulation,[],[f37,f73])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) | ~spl8_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f71])).
% 0.19/0.51  fof(f82,plain,(
% 0.19/0.51    spl8_5 | spl8_6 | spl8_7),
% 0.19/0.51    inference(avatar_split_clause,[],[f69,f79,f75,f71])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    k3_zfmisc_1(sK4,sK5,sK6) = k1_relat_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK7 | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)),
% 0.19/0.51    inference(superposition,[],[f25,f37])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.19/0.51    inference(avatar_split_clause,[],[f21,f60,f56,f52,f48])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (1864)------------------------------
% 0.19/0.51  % (1864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (1864)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (1864)Memory used [KB]: 10874
% 0.19/0.51  % (1864)Time elapsed: 0.101 s
% 0.19/0.51  % (1864)------------------------------
% 0.19/0.51  % (1864)------------------------------
% 0.19/0.51  % (1857)Success in time 0.165 s
%------------------------------------------------------------------------------
