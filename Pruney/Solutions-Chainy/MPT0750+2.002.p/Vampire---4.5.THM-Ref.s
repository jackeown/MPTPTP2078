%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:39 EST 2020

% Result     : Theorem 4.43s
% Output     : Refutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 338 expanded)
%              Number of leaves         :   35 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  603 (1489 expanded)
%              Number of equality atoms :   68 ( 142 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f153,f158,f162,f167,f511,f736,f737,f2160,f3007,f3069,f3089,f3206,f4239,f4318,f5080,f5181])).

fof(f5181,plain,
    ( ~ spl8_1
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f5180])).

fof(f5180,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f5179,f142])).

fof(f142,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f5179,plain,
    ( ~ v4_ordinal1(sK0)
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f5168,f178])).

fof(f178,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f100,f138])).

fof(f138,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f5168,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v4_ordinal1(sK0)
    | ~ spl8_11 ),
    inference(superposition,[],[f498,f116])).

fof(f116,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f498,plain,
    ( r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl8_11
  <=> r2_hidden(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f5080,plain,
    ( ~ spl8_3
    | ~ spl8_12
    | ~ spl8_128 ),
    inference(avatar_contradiction_clause,[],[f5079])).

fof(f5079,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_12
    | ~ spl8_128 ),
    inference(subsumption_resolution,[],[f5078,f152])).

fof(f152,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f5078,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl8_12
    | ~ spl8_128 ),
    inference(forward_demodulation,[],[f5077,f502])).

fof(f502,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl8_12
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f5077,plain,
    ( ~ r2_hidden(sK1,k3_tarski(sK0))
    | ~ spl8_128 ),
    inference(subsumption_resolution,[],[f5071,f178])).

fof(f5071,plain,
    ( r2_hidden(sK1,sK1)
    | ~ r2_hidden(sK1,k3_tarski(sK0))
    | ~ spl8_128 ),
    inference(superposition,[],[f137,f3740])).

fof(f3740,plain,
    ( sK1 = sK5(sK0,sK1)
    | ~ spl8_128 ),
    inference(avatar_component_clause,[],[f3738])).

fof(f3738,plain,
    ( spl8_128
  <=> sK1 = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).

fof(f137,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK3(X0,X1),X3) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( r2_hidden(sK4(X0,X1),X0)
              & r2_hidden(sK3(X0,X1),sK4(X0,X1)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK5(X0,X5),X0)
                & r2_hidden(X5,sK5(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f68,f71,f70,f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK3(X0,X1),X3) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK3(X0,X1),X4) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK3(X0,X1),X4) )
     => ( r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK5(X0,X5),X0)
        & r2_hidden(X5,sK5(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f4318,plain,
    ( spl8_128
    | ~ spl8_3
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f4317,f612,f500,f150,f3738])).

fof(f612,plain,
    ( spl8_20
  <=> sK0 = k1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f4317,plain,
    ( sK1 = sK5(sK0,sK1)
    | ~ spl8_3
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f4316,f152])).

fof(f4316,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK1 = sK5(sK0,sK1)
    | ~ spl8_3
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f4315,f502])).

fof(f4315,plain,
    ( sK1 = sK5(sK0,sK1)
    | ~ r2_hidden(sK1,k3_tarski(sK0))
    | ~ spl8_3
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f4307,f152])).

fof(f4307,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK1 = sK5(sK0,sK1)
    | ~ r2_hidden(sK1,k3_tarski(sK0))
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(resolution,[],[f4260,f243])).

fof(f243,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK5(X5,X4),X4)
      | ~ r2_hidden(X4,k3_tarski(X5)) ) ),
    inference(resolution,[],[f137,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f4260,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(sK0,X7),sK1)
        | ~ r2_hidden(X7,sK0)
        | sK1 = sK5(sK0,X7) )
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f3118,f502])).

fof(f3118,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(sK0,X7),sK1)
        | sK1 = sK5(sK0,X7)
        | ~ r2_hidden(X7,k3_tarski(sK0)) )
    | ~ spl8_20 ),
    inference(superposition,[],[f251,f614])).

fof(f614,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f612])).

fof(f251,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK5(k1_ordinal1(X3),X4),X3)
      | sK5(k1_ordinal1(X3),X4) = X3
      | ~ r2_hidden(X4,k3_tarski(k1_ordinal1(X3))) ) ),
    inference(resolution,[],[f86,f136])).

fof(f136,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f4239,plain,
    ( spl8_12
    | ~ spl8_6
    | ~ spl8_10
    | spl8_11 ),
    inference(avatar_split_clause,[],[f4238,f496,f492,f164,f500])).

fof(f164,plain,
    ( spl8_6
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f492,plain,
    ( spl8_10
  <=> v3_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f4238,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_6
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f4237,f166])).

fof(f166,plain,
    ( v3_ordinal1(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f4237,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f4236,f493])).

fof(f493,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f492])).

fof(f4236,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ v3_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(sK0)
    | spl8_11 ),
    inference(subsumption_resolution,[],[f4234,f952])).

fof(f952,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_tarski(X0)) ),
    inference(duplicate_literal_removal,[],[f950])).

fof(f950,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_tarski(X0))
      | ~ r2_hidden(X0,k3_tarski(X0)) ) ),
    inference(resolution,[],[f240,f137])).

fof(f240,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK5(X5,X4))
      | ~ r2_hidden(X4,k3_tarski(X5)) ) ),
    inference(resolution,[],[f136,f108])).

fof(f4234,plain,
    ( sK0 = k3_tarski(sK0)
    | r2_hidden(sK0,k3_tarski(sK0))
    | ~ v3_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(sK0)
    | spl8_11 ),
    inference(resolution,[],[f497,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f497,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f496])).

fof(f3206,plain,
    ( ~ spl8_3
    | ~ spl8_33 ),
    inference(avatar_contradiction_clause,[],[f3194])).

fof(f3194,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f152,f178,f913,f298])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f135,f127])).

fof(f127,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f135,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f913,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f911])).

fof(f911,plain,
    ( spl8_33
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f3089,plain,
    ( spl8_20
    | spl8_2
    | ~ spl8_6
    | ~ spl8_18
    | spl8_19 ),
    inference(avatar_split_clause,[],[f3088,f608,f604,f164,f145,f612])).

fof(f145,plain,
    ( spl8_2
  <=> r2_hidden(k1_ordinal1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f604,plain,
    ( spl8_18
  <=> v3_ordinal1(k1_ordinal1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f608,plain,
    ( spl8_19
  <=> r2_hidden(sK0,k1_ordinal1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f3088,plain,
    ( sK0 = k1_ordinal1(sK1)
    | spl8_2
    | ~ spl8_6
    | ~ spl8_18
    | spl8_19 ),
    inference(subsumption_resolution,[],[f3087,f605])).

fof(f605,plain,
    ( v3_ordinal1(k1_ordinal1(sK1))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f604])).

fof(f3087,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK1))
    | spl8_2
    | ~ spl8_6
    | spl8_19 ),
    inference(subsumption_resolution,[],[f3086,f166])).

fof(f3086,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK1))
    | spl8_2
    | spl8_19 ),
    inference(subsumption_resolution,[],[f3081,f147])).

fof(f147,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f145])).

fof(f3081,plain,
    ( sK0 = k1_ordinal1(sK1)
    | r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK1))
    | spl8_19 ),
    inference(resolution,[],[f609,f115])).

fof(f609,plain,
    ( ~ r2_hidden(sK0,k1_ordinal1(sK1))
    | spl8_19 ),
    inference(avatar_component_clause,[],[f608])).

fof(f3069,plain,
    ( ~ spl8_22
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f3061,f150,f747])).

fof(f747,plain,
    ( spl8_22
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f3061,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f152,f108])).

fof(f3007,plain,
    ( ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f3006])).

fof(f3006,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f3005,f498])).

fof(f3005,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f2986,f493])).

fof(f2986,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | ~ r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f532,f161])).

fof(f161,plain,
    ( ! [X2] :
        ( r2_hidden(k1_ordinal1(X2),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_5
  <=> ! [X2] :
        ( r2_hidden(k1_ordinal1(X2),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f532,plain,(
    ! [X11] : ~ r2_hidden(k1_ordinal1(k3_tarski(X11)),X11) ),
    inference(resolution,[],[f195,f131])).

fof(f131,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_tarski(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f107,f100])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f2160,plain,
    ( spl8_33
    | spl8_22
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1363,f608,f747,f911])).

fof(f1363,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl8_19 ),
    inference(resolution,[],[f335,f610])).

fof(f610,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK1))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f608])).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_ordinal1(X0))
      | r2_hidden(X1,X0)
      | r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(superposition,[],[f134,f92])).

fof(f92,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f134,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f64,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f737,plain,
    ( ~ spl8_4
    | spl8_18 ),
    inference(avatar_split_clause,[],[f624,f604,f155])).

fof(f155,plain,
    ( spl8_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f624,plain,
    ( ~ v3_ordinal1(sK1)
    | spl8_18 ),
    inference(resolution,[],[f606,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f606,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK1))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f604])).

fof(f736,plain,
    ( spl8_1
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f732,f500,f141])).

fof(f732,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f724])).

fof(f724,plain,
    ( sK0 != sK0
    | v4_ordinal1(sK0)
    | ~ spl8_12 ),
    inference(superposition,[],[f117,f502])).

fof(f117,plain,(
    ! [X0] :
      ( k3_tarski(X0) != X0
      | v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f511,plain,
    ( ~ spl8_6
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl8_6
    | spl8_10 ),
    inference(subsumption_resolution,[],[f507,f166])).

fof(f507,plain,
    ( ~ v3_ordinal1(sK0)
    | spl8_10 ),
    inference(resolution,[],[f494,f121])).

fof(f121,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f494,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f492])).

fof(f167,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f81,f164])).

fof(f81,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
        & r2_hidden(sK1,sK0)
        & v3_ordinal1(sK1) )
      | ~ v4_ordinal1(sK0) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK0)
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK0) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK0)
            & r2_hidden(X1,sK0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK0)
            | ~ r2_hidden(X2,sK0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK0) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK0)
        & r2_hidden(X1,sK0)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
      & r2_hidden(sK1,sK0)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f162,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f82,f160,f141])).

fof(f82,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f158,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f83,f155,f141])).

fof(f83,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f153,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f84,f150,f141])).

fof(f84,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f148,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f85,f145,f141])).

fof(f85,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (31008)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (31024)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.52  % (31015)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (31006)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (31013)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (31007)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (31015)Refutation not found, incomplete strategy% (31015)------------------------------
% 0.22/0.53  % (31015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31009)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (31002)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (31015)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31015)Memory used [KB]: 10746
% 0.22/0.53  % (31015)Time elapsed: 0.107 s
% 0.22/0.53  % (31015)------------------------------
% 0.22/0.53  % (31015)------------------------------
% 0.22/0.53  % (31027)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (30999)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (31009)Refutation not found, incomplete strategy% (31009)------------------------------
% 0.22/0.54  % (31009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31009)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31009)Memory used [KB]: 10874
% 0.22/0.54  % (31009)Time elapsed: 0.116 s
% 0.22/0.54  % (31009)------------------------------
% 0.22/0.54  % (31009)------------------------------
% 0.22/0.54  % (31001)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (31026)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (31000)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (31025)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (31003)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (31012)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (31021)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (31019)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (31018)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (31004)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (31016)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.55  % (31020)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.55  % (31023)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.49/0.55  % (31022)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.49/0.55  % (31028)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.49/0.55  % (31017)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.49/0.55  % (31010)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.49/0.56  % (31014)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.49/0.56  % (31005)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.56  % (31027)Refutation not found, incomplete strategy% (31027)------------------------------
% 1.49/0.56  % (31027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (31027)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (31027)Memory used [KB]: 10874
% 1.49/0.56  % (31027)Time elapsed: 0.124 s
% 1.49/0.56  % (31027)------------------------------
% 1.49/0.56  % (31027)------------------------------
% 1.49/0.56  % (31011)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.23/0.69  % (31029)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.23/0.70  % (31031)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.23/0.70  % (31030)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.06/0.84  % (31001)Time limit reached!
% 3.06/0.84  % (31001)------------------------------
% 3.06/0.84  % (31001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.84  % (31001)Termination reason: Time limit
% 3.06/0.84  
% 3.06/0.84  % (31001)Memory used [KB]: 6652
% 3.06/0.84  % (31001)Time elapsed: 0.415 s
% 3.06/0.84  % (31001)------------------------------
% 3.06/0.84  % (31001)------------------------------
% 3.06/0.84  % (31023)Time limit reached!
% 3.06/0.84  % (31023)------------------------------
% 3.06/0.84  % (31023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.84  % (31023)Termination reason: Time limit
% 3.06/0.84  
% 3.06/0.84  % (31023)Memory used [KB]: 12281
% 3.06/0.84  % (31023)Time elapsed: 0.418 s
% 3.06/0.84  % (31023)------------------------------
% 3.06/0.84  % (31023)------------------------------
% 3.86/0.92  % (31005)Time limit reached!
% 3.86/0.92  % (31005)------------------------------
% 3.86/0.92  % (31005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.92  % (31005)Termination reason: Time limit
% 3.86/0.92  % (31005)Termination phase: Saturation
% 3.86/0.92  
% 3.86/0.92  % (31005)Memory used [KB]: 14200
% 3.86/0.92  % (31005)Time elapsed: 0.508 s
% 3.86/0.92  % (31005)------------------------------
% 3.86/0.92  % (31005)------------------------------
% 4.24/0.93  % (31013)Time limit reached!
% 4.24/0.93  % (31013)------------------------------
% 4.24/0.93  % (31013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.93  % (31013)Termination reason: Time limit
% 4.24/0.93  
% 4.24/0.93  % (31013)Memory used [KB]: 4477
% 4.24/0.93  % (31013)Time elapsed: 0.517 s
% 4.24/0.93  % (31013)------------------------------
% 4.24/0.93  % (31013)------------------------------
% 4.24/0.94  % (31028)Time limit reached!
% 4.24/0.94  % (31028)------------------------------
% 4.24/0.94  % (31028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.94  % (31028)Termination reason: Time limit
% 4.24/0.94  % (31028)Termination phase: Saturation
% 4.24/0.94  
% 4.24/0.94  % (31028)Memory used [KB]: 2174
% 4.24/0.94  % (31028)Time elapsed: 0.500 s
% 4.24/0.94  % (31028)------------------------------
% 4.24/0.94  % (31028)------------------------------
% 4.43/0.97  % (31033)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.43/0.98  % (31032)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.43/0.98  % (31020)Refutation found. Thanks to Tanya!
% 4.43/0.98  % SZS status Theorem for theBenchmark
% 4.43/0.98  % SZS output start Proof for theBenchmark
% 4.43/0.98  fof(f5182,plain,(
% 4.43/0.98    $false),
% 4.43/0.98    inference(avatar_sat_refutation,[],[f148,f153,f158,f162,f167,f511,f736,f737,f2160,f3007,f3069,f3089,f3206,f4239,f4318,f5080,f5181])).
% 4.43/0.98  fof(f5181,plain,(
% 4.43/0.98    ~spl8_1 | ~spl8_11),
% 4.43/0.98    inference(avatar_contradiction_clause,[],[f5180])).
% 4.43/0.98  fof(f5180,plain,(
% 4.43/0.98    $false | (~spl8_1 | ~spl8_11)),
% 4.43/0.98    inference(subsumption_resolution,[],[f5179,f142])).
% 4.43/0.98  fof(f142,plain,(
% 4.43/0.98    v4_ordinal1(sK0) | ~spl8_1),
% 4.43/0.98    inference(avatar_component_clause,[],[f141])).
% 4.43/0.98  fof(f141,plain,(
% 4.43/0.98    spl8_1 <=> v4_ordinal1(sK0)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 4.43/0.98  fof(f5179,plain,(
% 4.43/0.98    ~v4_ordinal1(sK0) | ~spl8_11),
% 4.43/0.98    inference(subsumption_resolution,[],[f5168,f178])).
% 4.43/0.98  fof(f178,plain,(
% 4.43/0.98    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 4.43/0.98    inference(resolution,[],[f100,f138])).
% 4.43/0.98  fof(f138,plain,(
% 4.43/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.43/0.98    inference(equality_resolution,[],[f123])).
% 4.43/0.98  fof(f123,plain,(
% 4.43/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.43/0.98    inference(cnf_transformation,[],[f80])).
% 4.43/0.98  fof(f80,plain,(
% 4.43/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.43/0.98    inference(flattening,[],[f79])).
% 4.43/0.98  fof(f79,plain,(
% 4.43/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.43/0.98    inference(nnf_transformation,[],[f3])).
% 4.43/0.98  fof(f3,axiom,(
% 4.43/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.43/0.98  fof(f100,plain,(
% 4.43/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.43/0.98    inference(cnf_transformation,[],[f35])).
% 4.43/0.98  fof(f35,plain,(
% 4.43/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 4.43/0.98    inference(ennf_transformation,[],[f26])).
% 4.43/0.98  fof(f26,axiom,(
% 4.43/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 4.43/0.98  fof(f5168,plain,(
% 4.43/0.98    r2_hidden(sK0,sK0) | ~v4_ordinal1(sK0) | ~spl8_11),
% 4.43/0.98    inference(superposition,[],[f498,f116])).
% 4.43/0.98  fof(f116,plain,(
% 4.43/0.98    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 4.43/0.98    inference(cnf_transformation,[],[f77])).
% 4.43/0.98  fof(f77,plain,(
% 4.43/0.98    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 4.43/0.98    inference(nnf_transformation,[],[f15])).
% 4.43/0.98  fof(f15,axiom,(
% 4.43/0.98    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 4.43/0.98  fof(f498,plain,(
% 4.43/0.98    r2_hidden(k3_tarski(sK0),sK0) | ~spl8_11),
% 4.43/0.98    inference(avatar_component_clause,[],[f496])).
% 4.43/0.98  fof(f496,plain,(
% 4.43/0.98    spl8_11 <=> r2_hidden(k3_tarski(sK0),sK0)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 4.43/0.98  fof(f5080,plain,(
% 4.43/0.98    ~spl8_3 | ~spl8_12 | ~spl8_128),
% 4.43/0.98    inference(avatar_contradiction_clause,[],[f5079])).
% 4.43/0.98  fof(f5079,plain,(
% 4.43/0.98    $false | (~spl8_3 | ~spl8_12 | ~spl8_128)),
% 4.43/0.98    inference(subsumption_resolution,[],[f5078,f152])).
% 4.43/0.98  fof(f152,plain,(
% 4.43/0.98    r2_hidden(sK1,sK0) | ~spl8_3),
% 4.43/0.98    inference(avatar_component_clause,[],[f150])).
% 4.43/0.98  fof(f150,plain,(
% 4.43/0.98    spl8_3 <=> r2_hidden(sK1,sK0)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 4.43/0.98  fof(f5078,plain,(
% 4.43/0.98    ~r2_hidden(sK1,sK0) | (~spl8_12 | ~spl8_128)),
% 4.43/0.98    inference(forward_demodulation,[],[f5077,f502])).
% 4.43/0.98  fof(f502,plain,(
% 4.43/0.98    sK0 = k3_tarski(sK0) | ~spl8_12),
% 4.43/0.98    inference(avatar_component_clause,[],[f500])).
% 4.43/0.98  fof(f500,plain,(
% 4.43/0.98    spl8_12 <=> sK0 = k3_tarski(sK0)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 4.43/0.98  fof(f5077,plain,(
% 4.43/0.98    ~r2_hidden(sK1,k3_tarski(sK0)) | ~spl8_128),
% 4.43/0.98    inference(subsumption_resolution,[],[f5071,f178])).
% 4.43/0.98  fof(f5071,plain,(
% 4.43/0.98    r2_hidden(sK1,sK1) | ~r2_hidden(sK1,k3_tarski(sK0)) | ~spl8_128),
% 4.43/0.98    inference(superposition,[],[f137,f3740])).
% 4.43/0.98  fof(f3740,plain,(
% 4.43/0.98    sK1 = sK5(sK0,sK1) | ~spl8_128),
% 4.43/0.98    inference(avatar_component_clause,[],[f3738])).
% 4.43/0.98  fof(f3738,plain,(
% 4.43/0.98    spl8_128 <=> sK1 = sK5(sK0,sK1)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).
% 4.43/0.98  fof(f137,plain,(
% 4.43/0.98    ( ! [X0,X5] : (r2_hidden(X5,sK5(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 4.43/0.98    inference(equality_resolution,[],[f101])).
% 4.43/0.98  fof(f101,plain,(
% 4.43/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,sK5(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 4.43/0.98    inference(cnf_transformation,[],[f72])).
% 4.43/0.98  fof(f72,plain,(
% 4.43/0.98    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & ((r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 4.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f68,f71,f70,f69])).
% 4.43/0.98  fof(f69,plain,(
% 4.43/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) | r2_hidden(sK3(X0,X1),X1))))),
% 4.43/0.98    introduced(choice_axiom,[])).
% 4.43/0.98  fof(f70,plain,(
% 4.43/0.98    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) => (r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))))),
% 4.43/0.98    introduced(choice_axiom,[])).
% 4.43/0.98  fof(f71,plain,(
% 4.43/0.98    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))))),
% 4.43/0.98    introduced(choice_axiom,[])).
% 4.43/0.98  fof(f68,plain,(
% 4.43/0.98    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 4.43/0.98    inference(rectify,[],[f67])).
% 4.43/0.98  fof(f67,plain,(
% 4.43/0.98    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 4.43/0.98    inference(nnf_transformation,[],[f7])).
% 4.43/0.98  fof(f7,axiom,(
% 4.43/0.98    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 4.43/0.98  fof(f4318,plain,(
% 4.43/0.98    spl8_128 | ~spl8_3 | ~spl8_12 | ~spl8_20),
% 4.43/0.98    inference(avatar_split_clause,[],[f4317,f612,f500,f150,f3738])).
% 4.43/0.98  fof(f612,plain,(
% 4.43/0.98    spl8_20 <=> sK0 = k1_ordinal1(sK1)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 4.43/0.98  fof(f4317,plain,(
% 4.43/0.98    sK1 = sK5(sK0,sK1) | (~spl8_3 | ~spl8_12 | ~spl8_20)),
% 4.43/0.98    inference(subsumption_resolution,[],[f4316,f152])).
% 4.43/0.98  fof(f4316,plain,(
% 4.43/0.98    ~r2_hidden(sK1,sK0) | sK1 = sK5(sK0,sK1) | (~spl8_3 | ~spl8_12 | ~spl8_20)),
% 4.43/0.98    inference(forward_demodulation,[],[f4315,f502])).
% 4.43/0.98  fof(f4315,plain,(
% 4.43/0.98    sK1 = sK5(sK0,sK1) | ~r2_hidden(sK1,k3_tarski(sK0)) | (~spl8_3 | ~spl8_12 | ~spl8_20)),
% 4.43/0.98    inference(subsumption_resolution,[],[f4307,f152])).
% 4.43/0.98  fof(f4307,plain,(
% 4.43/0.98    ~r2_hidden(sK1,sK0) | sK1 = sK5(sK0,sK1) | ~r2_hidden(sK1,k3_tarski(sK0)) | (~spl8_12 | ~spl8_20)),
% 4.43/0.98    inference(resolution,[],[f4260,f243])).
% 4.43/0.98  fof(f243,plain,(
% 4.43/0.98    ( ! [X4,X5] : (~r2_hidden(sK5(X5,X4),X4) | ~r2_hidden(X4,k3_tarski(X5))) )),
% 4.43/0.98    inference(resolution,[],[f137,f108])).
% 4.43/0.98  fof(f108,plain,(
% 4.43/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.43/0.98    inference(cnf_transformation,[],[f37])).
% 4.43/0.98  fof(f37,plain,(
% 4.43/0.98    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 4.43/0.98    inference(ennf_transformation,[],[f1])).
% 4.43/0.98  fof(f1,axiom,(
% 4.43/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 4.43/0.98  fof(f4260,plain,(
% 4.43/0.98    ( ! [X7] : (r2_hidden(sK5(sK0,X7),sK1) | ~r2_hidden(X7,sK0) | sK1 = sK5(sK0,X7)) ) | (~spl8_12 | ~spl8_20)),
% 4.43/0.98    inference(backward_demodulation,[],[f3118,f502])).
% 4.43/0.98  fof(f3118,plain,(
% 4.43/0.98    ( ! [X7] : (r2_hidden(sK5(sK0,X7),sK1) | sK1 = sK5(sK0,X7) | ~r2_hidden(X7,k3_tarski(sK0))) ) | ~spl8_20),
% 4.43/0.98    inference(superposition,[],[f251,f614])).
% 4.43/0.98  fof(f614,plain,(
% 4.43/0.98    sK0 = k1_ordinal1(sK1) | ~spl8_20),
% 4.43/0.98    inference(avatar_component_clause,[],[f612])).
% 4.43/0.98  fof(f251,plain,(
% 4.43/0.98    ( ! [X4,X3] : (r2_hidden(sK5(k1_ordinal1(X3),X4),X3) | sK5(k1_ordinal1(X3),X4) = X3 | ~r2_hidden(X4,k3_tarski(k1_ordinal1(X3)))) )),
% 4.43/0.98    inference(resolution,[],[f86,f136])).
% 4.43/0.98  fof(f136,plain,(
% 4.43/0.98    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 4.43/0.98    inference(equality_resolution,[],[f102])).
% 4.43/0.98  fof(f102,plain,(
% 4.43/0.98    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 4.43/0.98    inference(cnf_transformation,[],[f72])).
% 4.43/0.98  fof(f86,plain,(
% 4.43/0.98    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 4.43/0.98    inference(cnf_transformation,[],[f60])).
% 4.43/0.98  fof(f60,plain,(
% 4.43/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 4.43/0.98    inference(flattening,[],[f59])).
% 4.43/0.98  fof(f59,plain,(
% 4.43/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 4.43/0.98    inference(nnf_transformation,[],[f17])).
% 4.43/0.98  fof(f17,axiom,(
% 4.43/0.98    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 4.43/0.98  fof(f4239,plain,(
% 4.43/0.98    spl8_12 | ~spl8_6 | ~spl8_10 | spl8_11),
% 4.43/0.98    inference(avatar_split_clause,[],[f4238,f496,f492,f164,f500])).
% 4.43/0.98  fof(f164,plain,(
% 4.43/0.98    spl8_6 <=> v3_ordinal1(sK0)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 4.43/0.98  fof(f492,plain,(
% 4.43/0.98    spl8_10 <=> v3_ordinal1(k3_tarski(sK0))),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 4.43/0.98  fof(f4238,plain,(
% 4.43/0.98    sK0 = k3_tarski(sK0) | (~spl8_6 | ~spl8_10 | spl8_11)),
% 4.43/0.98    inference(subsumption_resolution,[],[f4237,f166])).
% 4.43/0.98  fof(f166,plain,(
% 4.43/0.98    v3_ordinal1(sK0) | ~spl8_6),
% 4.43/0.98    inference(avatar_component_clause,[],[f164])).
% 4.43/0.98  fof(f4237,plain,(
% 4.43/0.98    sK0 = k3_tarski(sK0) | ~v3_ordinal1(sK0) | (~spl8_10 | spl8_11)),
% 4.43/0.98    inference(subsumption_resolution,[],[f4236,f493])).
% 4.43/0.98  fof(f493,plain,(
% 4.43/0.98    v3_ordinal1(k3_tarski(sK0)) | ~spl8_10),
% 4.43/0.98    inference(avatar_component_clause,[],[f492])).
% 4.43/0.98  fof(f4236,plain,(
% 4.43/0.98    sK0 = k3_tarski(sK0) | ~v3_ordinal1(k3_tarski(sK0)) | ~v3_ordinal1(sK0) | spl8_11),
% 4.43/0.98    inference(subsumption_resolution,[],[f4234,f952])).
% 4.43/0.98  fof(f952,plain,(
% 4.43/0.98    ( ! [X0] : (~r2_hidden(X0,k3_tarski(X0))) )),
% 4.43/0.98    inference(duplicate_literal_removal,[],[f950])).
% 4.43/0.98  fof(f950,plain,(
% 4.43/0.98    ( ! [X0] : (~r2_hidden(X0,k3_tarski(X0)) | ~r2_hidden(X0,k3_tarski(X0))) )),
% 4.43/0.98    inference(resolution,[],[f240,f137])).
% 4.43/0.98  fof(f240,plain,(
% 4.43/0.98    ( ! [X4,X5] : (~r2_hidden(X5,sK5(X5,X4)) | ~r2_hidden(X4,k3_tarski(X5))) )),
% 4.43/0.98    inference(resolution,[],[f136,f108])).
% 4.43/0.98  fof(f4234,plain,(
% 4.43/0.98    sK0 = k3_tarski(sK0) | r2_hidden(sK0,k3_tarski(sK0)) | ~v3_ordinal1(k3_tarski(sK0)) | ~v3_ordinal1(sK0) | spl8_11),
% 4.43/0.98    inference(resolution,[],[f497,f115])).
% 4.43/0.98  fof(f115,plain,(
% 4.43/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 4.43/0.98    inference(cnf_transformation,[],[f44])).
% 4.43/0.98  fof(f44,plain,(
% 4.43/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 4.43/0.98    inference(flattening,[],[f43])).
% 4.43/0.98  fof(f43,plain,(
% 4.43/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 4.43/0.98    inference(ennf_transformation,[],[f20])).
% 4.43/0.98  fof(f20,axiom,(
% 4.43/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 4.43/0.98  fof(f497,plain,(
% 4.43/0.98    ~r2_hidden(k3_tarski(sK0),sK0) | spl8_11),
% 4.43/0.98    inference(avatar_component_clause,[],[f496])).
% 4.43/0.98  fof(f3206,plain,(
% 4.43/0.98    ~spl8_3 | ~spl8_33),
% 4.43/0.98    inference(avatar_contradiction_clause,[],[f3194])).
% 4.43/0.98  fof(f3194,plain,(
% 4.43/0.98    $false | (~spl8_3 | ~spl8_33)),
% 4.43/0.98    inference(unit_resulting_resolution,[],[f152,f178,f913,f298])).
% 4.43/0.98  fof(f298,plain,(
% 4.43/0.98    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_tarski(X0)) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 4.43/0.98    inference(superposition,[],[f135,f127])).
% 4.43/0.98  fof(f127,plain,(
% 4.43/0.98    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 4.43/0.98    inference(cnf_transformation,[],[f9])).
% 4.43/0.98  fof(f9,axiom,(
% 4.43/0.98    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 4.43/0.98  fof(f135,plain,(
% 4.43/0.98    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 4.43/0.98    inference(equality_resolution,[],[f103])).
% 4.43/0.98  fof(f103,plain,(
% 4.43/0.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 4.43/0.98    inference(cnf_transformation,[],[f72])).
% 4.43/0.98  fof(f913,plain,(
% 4.43/0.98    r2_hidden(sK0,k1_tarski(sK1)) | ~spl8_33),
% 4.43/0.98    inference(avatar_component_clause,[],[f911])).
% 4.43/0.98  fof(f911,plain,(
% 4.43/0.98    spl8_33 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 4.43/0.98  fof(f3089,plain,(
% 4.43/0.98    spl8_20 | spl8_2 | ~spl8_6 | ~spl8_18 | spl8_19),
% 4.43/0.98    inference(avatar_split_clause,[],[f3088,f608,f604,f164,f145,f612])).
% 4.43/0.98  fof(f145,plain,(
% 4.43/0.98    spl8_2 <=> r2_hidden(k1_ordinal1(sK1),sK0)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 4.43/0.98  fof(f604,plain,(
% 4.43/0.98    spl8_18 <=> v3_ordinal1(k1_ordinal1(sK1))),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 4.43/0.98  fof(f608,plain,(
% 4.43/0.98    spl8_19 <=> r2_hidden(sK0,k1_ordinal1(sK1))),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 4.43/0.98  fof(f3088,plain,(
% 4.43/0.98    sK0 = k1_ordinal1(sK1) | (spl8_2 | ~spl8_6 | ~spl8_18 | spl8_19)),
% 4.43/0.98    inference(subsumption_resolution,[],[f3087,f605])).
% 4.43/0.98  fof(f605,plain,(
% 4.43/0.98    v3_ordinal1(k1_ordinal1(sK1)) | ~spl8_18),
% 4.43/0.98    inference(avatar_component_clause,[],[f604])).
% 4.43/0.98  fof(f3087,plain,(
% 4.43/0.98    sK0 = k1_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK1)) | (spl8_2 | ~spl8_6 | spl8_19)),
% 4.43/0.98    inference(subsumption_resolution,[],[f3086,f166])).
% 4.43/0.98  fof(f3086,plain,(
% 4.43/0.98    sK0 = k1_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k1_ordinal1(sK1)) | (spl8_2 | spl8_19)),
% 4.43/0.98    inference(subsumption_resolution,[],[f3081,f147])).
% 4.43/0.98  fof(f147,plain,(
% 4.43/0.98    ~r2_hidden(k1_ordinal1(sK1),sK0) | spl8_2),
% 4.43/0.98    inference(avatar_component_clause,[],[f145])).
% 4.43/0.98  fof(f3081,plain,(
% 4.43/0.98    sK0 = k1_ordinal1(sK1) | r2_hidden(k1_ordinal1(sK1),sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k1_ordinal1(sK1)) | spl8_19),
% 4.43/0.98    inference(resolution,[],[f609,f115])).
% 4.43/0.98  fof(f609,plain,(
% 4.43/0.98    ~r2_hidden(sK0,k1_ordinal1(sK1)) | spl8_19),
% 4.43/0.98    inference(avatar_component_clause,[],[f608])).
% 4.43/0.98  fof(f3069,plain,(
% 4.43/0.98    ~spl8_22 | ~spl8_3),
% 4.43/0.98    inference(avatar_split_clause,[],[f3061,f150,f747])).
% 4.43/0.98  fof(f747,plain,(
% 4.43/0.98    spl8_22 <=> r2_hidden(sK0,sK1)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 4.43/0.98  fof(f3061,plain,(
% 4.43/0.98    ~r2_hidden(sK0,sK1) | ~spl8_3),
% 4.43/0.98    inference(resolution,[],[f152,f108])).
% 4.43/0.98  fof(f3007,plain,(
% 4.43/0.98    ~spl8_5 | ~spl8_10 | ~spl8_11),
% 4.43/0.98    inference(avatar_contradiction_clause,[],[f3006])).
% 4.43/0.98  fof(f3006,plain,(
% 4.43/0.98    $false | (~spl8_5 | ~spl8_10 | ~spl8_11)),
% 4.43/0.98    inference(subsumption_resolution,[],[f3005,f498])).
% 4.43/0.98  fof(f3005,plain,(
% 4.43/0.98    ~r2_hidden(k3_tarski(sK0),sK0) | (~spl8_5 | ~spl8_10)),
% 4.43/0.98    inference(subsumption_resolution,[],[f2986,f493])).
% 4.43/0.98  fof(f2986,plain,(
% 4.43/0.98    ~v3_ordinal1(k3_tarski(sK0)) | ~r2_hidden(k3_tarski(sK0),sK0) | ~spl8_5),
% 4.43/0.98    inference(resolution,[],[f532,f161])).
% 4.43/0.98  fof(f161,plain,(
% 4.43/0.98    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 4.43/0.98    inference(avatar_component_clause,[],[f160])).
% 4.43/0.98  fof(f160,plain,(
% 4.43/0.98    spl8_5 <=> ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 4.43/0.98  fof(f532,plain,(
% 4.43/0.98    ( ! [X11] : (~r2_hidden(k1_ordinal1(k3_tarski(X11)),X11)) )),
% 4.43/0.98    inference(resolution,[],[f195,f131])).
% 4.43/0.98  fof(f131,plain,(
% 4.43/0.98    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 4.43/0.98    inference(equality_resolution,[],[f88])).
% 4.43/0.98  fof(f88,plain,(
% 4.43/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 4.43/0.98    inference(cnf_transformation,[],[f60])).
% 4.43/0.98  fof(f195,plain,(
% 4.43/0.98    ( ! [X0,X1] : (~r2_hidden(k3_tarski(X1),X0) | ~r2_hidden(X0,X1)) )),
% 4.43/0.98    inference(resolution,[],[f107,f100])).
% 4.43/0.98  fof(f107,plain,(
% 4.43/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 4.43/0.98    inference(cnf_transformation,[],[f36])).
% 4.43/0.98  fof(f36,plain,(
% 4.43/0.98    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 4.43/0.98    inference(ennf_transformation,[],[f8])).
% 4.43/0.98  fof(f8,axiom,(
% 4.43/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 4.43/0.98  fof(f2160,plain,(
% 4.43/0.98    spl8_33 | spl8_22 | ~spl8_19),
% 4.43/0.98    inference(avatar_split_clause,[],[f1363,f608,f747,f911])).
% 4.43/0.98  fof(f1363,plain,(
% 4.43/0.98    r2_hidden(sK0,sK1) | r2_hidden(sK0,k1_tarski(sK1)) | ~spl8_19),
% 4.43/0.98    inference(resolution,[],[f335,f610])).
% 4.43/0.98  fof(f610,plain,(
% 4.43/0.98    r2_hidden(sK0,k1_ordinal1(sK1)) | ~spl8_19),
% 4.43/0.98    inference(avatar_component_clause,[],[f608])).
% 4.43/0.98  fof(f335,plain,(
% 4.43/0.98    ( ! [X0,X1] : (~r2_hidden(X1,k1_ordinal1(X0)) | r2_hidden(X1,X0) | r2_hidden(X1,k1_tarski(X0))) )),
% 4.43/0.98    inference(superposition,[],[f134,f92])).
% 4.43/0.98  fof(f92,plain,(
% 4.43/0.98    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 4.43/0.98    inference(cnf_transformation,[],[f13])).
% 4.43/0.98  fof(f13,axiom,(
% 4.43/0.98    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 4.43/0.98  fof(f134,plain,(
% 4.43/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 4.43/0.98    inference(equality_resolution,[],[f94])).
% 4.43/0.98  fof(f94,plain,(
% 4.43/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 4.43/0.98    inference(cnf_transformation,[],[f66])).
% 4.43/0.98  fof(f66,plain,(
% 4.43/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f64,f65])).
% 4.43/0.98  fof(f65,plain,(
% 4.43/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 4.43/0.98    introduced(choice_axiom,[])).
% 4.43/0.98  fof(f64,plain,(
% 4.43/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.43/0.98    inference(rectify,[],[f63])).
% 4.43/0.98  fof(f63,plain,(
% 4.43/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.43/0.98    inference(flattening,[],[f62])).
% 4.43/0.98  fof(f62,plain,(
% 4.43/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.43/0.98    inference(nnf_transformation,[],[f2])).
% 4.43/0.98  fof(f2,axiom,(
% 4.43/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 4.43/0.98  fof(f737,plain,(
% 4.43/0.98    ~spl8_4 | spl8_18),
% 4.43/0.98    inference(avatar_split_clause,[],[f624,f604,f155])).
% 4.43/0.98  fof(f155,plain,(
% 4.43/0.98    spl8_4 <=> v3_ordinal1(sK1)),
% 4.43/0.98    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 4.43/0.98  fof(f624,plain,(
% 4.43/0.98    ~v3_ordinal1(sK1) | spl8_18),
% 4.43/0.98    inference(resolution,[],[f606,f91])).
% 4.43/0.98  fof(f91,plain,(
% 4.43/0.98    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 4.43/0.98    inference(cnf_transformation,[],[f34])).
% 4.43/0.98  fof(f34,plain,(
% 4.43/0.98    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 4.43/0.98    inference(ennf_transformation,[],[f21])).
% 4.43/0.98  fof(f21,axiom,(
% 4.43/0.98    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 4.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 4.43/0.98  fof(f606,plain,(
% 4.43/0.98    ~v3_ordinal1(k1_ordinal1(sK1)) | spl8_18),
% 4.43/0.98    inference(avatar_component_clause,[],[f604])).
% 4.43/0.98  fof(f736,plain,(
% 4.43/0.98    spl8_1 | ~spl8_12),
% 4.43/0.98    inference(avatar_split_clause,[],[f732,f500,f141])).
% 4.43/0.98  fof(f732,plain,(
% 4.43/0.98    v4_ordinal1(sK0) | ~spl8_12),
% 4.43/0.98    inference(trivial_inequality_removal,[],[f724])).
% 4.43/0.98  fof(f724,plain,(
% 4.43/0.98    sK0 != sK0 | v4_ordinal1(sK0) | ~spl8_12),
% 4.43/0.98    inference(superposition,[],[f117,f502])).
% 4.43/0.98  fof(f117,plain,(
% 4.43/0.98    ( ! [X0] : (k3_tarski(X0) != X0 | v4_ordinal1(X0)) )),
% 4.43/0.98    inference(cnf_transformation,[],[f77])).
% 4.43/0.98  fof(f511,plain,(
% 4.43/0.99    ~spl8_6 | spl8_10),
% 4.43/0.99    inference(avatar_contradiction_clause,[],[f510])).
% 4.43/0.99  fof(f510,plain,(
% 4.43/0.99    $false | (~spl8_6 | spl8_10)),
% 4.43/0.99    inference(subsumption_resolution,[],[f507,f166])).
% 4.43/0.99  fof(f507,plain,(
% 4.43/0.99    ~v3_ordinal1(sK0) | spl8_10),
% 4.43/0.99    inference(resolution,[],[f494,f121])).
% 4.43/0.99  fof(f121,plain,(
% 4.43/0.99    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(X0)) )),
% 4.43/0.99    inference(cnf_transformation,[],[f49])).
% 4.43/0.99  fof(f49,plain,(
% 4.43/0.99    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(X0))),
% 4.43/0.99    inference(ennf_transformation,[],[f22])).
% 4.43/0.99  fof(f22,axiom,(
% 4.43/0.99    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 4.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).
% 4.43/0.99  fof(f494,plain,(
% 4.43/0.99    ~v3_ordinal1(k3_tarski(sK0)) | spl8_10),
% 4.43/0.99    inference(avatar_component_clause,[],[f492])).
% 4.43/0.99  fof(f167,plain,(
% 4.43/0.99    spl8_6),
% 4.43/0.99    inference(avatar_split_clause,[],[f81,f164])).
% 4.43/0.99  fof(f81,plain,(
% 4.43/0.99    v3_ordinal1(sK0)),
% 4.43/0.99    inference(cnf_transformation,[],[f58])).
% 4.43/0.99  fof(f58,plain,(
% 4.43/0.99    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 4.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).
% 4.43/0.99  fof(f56,plain,(
% 4.43/0.99    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 4.43/0.99    introduced(choice_axiom,[])).
% 4.43/0.99  fof(f57,plain,(
% 4.43/0.99    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 4.43/0.99    introduced(choice_axiom,[])).
% 4.43/0.99  fof(f55,plain,(
% 4.43/0.99    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 4.43/0.99    inference(rectify,[],[f54])).
% 4.43/0.99  fof(f54,plain,(
% 4.43/0.99    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 4.43/0.99    inference(flattening,[],[f53])).
% 4.43/0.99  fof(f53,plain,(
% 4.43/0.99    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 4.43/0.99    inference(nnf_transformation,[],[f32])).
% 4.43/0.99  fof(f32,plain,(
% 4.43/0.99    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 4.43/0.99    inference(flattening,[],[f31])).
% 4.43/0.99  fof(f31,plain,(
% 4.43/0.99    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 4.43/0.99    inference(ennf_transformation,[],[f28])).
% 4.43/0.99  fof(f28,negated_conjecture,(
% 4.43/0.99    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 4.43/0.99    inference(negated_conjecture,[],[f27])).
% 4.43/0.99  fof(f27,conjecture,(
% 4.43/0.99    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 4.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 4.43/0.99  fof(f162,plain,(
% 4.43/0.99    spl8_1 | spl8_5),
% 4.43/0.99    inference(avatar_split_clause,[],[f82,f160,f141])).
% 4.43/0.99  fof(f82,plain,(
% 4.43/0.99    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 4.43/0.99    inference(cnf_transformation,[],[f58])).
% 4.43/0.99  fof(f158,plain,(
% 4.43/0.99    ~spl8_1 | spl8_4),
% 4.43/0.99    inference(avatar_split_clause,[],[f83,f155,f141])).
% 4.43/0.99  fof(f83,plain,(
% 4.43/0.99    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 4.43/0.99    inference(cnf_transformation,[],[f58])).
% 4.43/0.99  fof(f153,plain,(
% 4.43/0.99    ~spl8_1 | spl8_3),
% 4.43/0.99    inference(avatar_split_clause,[],[f84,f150,f141])).
% 4.43/0.99  fof(f84,plain,(
% 4.43/0.99    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 4.43/0.99    inference(cnf_transformation,[],[f58])).
% 4.43/0.99  fof(f148,plain,(
% 4.43/0.99    ~spl8_1 | ~spl8_2),
% 4.43/0.99    inference(avatar_split_clause,[],[f85,f145,f141])).
% 4.43/0.99  fof(f85,plain,(
% 4.43/0.99    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 4.43/0.99    inference(cnf_transformation,[],[f58])).
% 4.43/0.99  % SZS output end Proof for theBenchmark
% 4.43/0.99  % (31020)------------------------------
% 4.43/0.99  % (31020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.99  % (31020)Termination reason: Refutation
% 4.43/0.99  
% 4.43/0.99  % (31020)Memory used [KB]: 9338
% 4.43/0.99  % (31020)Time elapsed: 0.554 s
% 4.43/0.99  % (31020)------------------------------
% 4.43/0.99  % (31020)------------------------------
% 4.43/0.99  % (30998)Success in time 0.619 s
%------------------------------------------------------------------------------
