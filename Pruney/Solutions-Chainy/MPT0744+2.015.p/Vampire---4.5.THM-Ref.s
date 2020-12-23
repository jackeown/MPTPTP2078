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
% DateTime   : Thu Dec  3 12:55:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 198 expanded)
%              Number of leaves         :   24 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  403 ( 856 expanded)
%              Number of equality atoms :   55 ( 102 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f93,f94,f142,f150,f155,f163,f169,f174,f185,f186,f196,f206,f234,f239])).

fof(f239,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f71,f233])).

fof(f233,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl4_14
  <=> r2_hidden(sK0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f234,plain,
    ( ~ spl4_14
    | spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f213,f182,f152,f231])).

fof(f152,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f182,plain,
    ( spl4_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f213,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl4_8
    | ~ spl4_10 ),
    inference(superposition,[],[f154,f184])).

fof(f184,plain,
    ( sK0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f182])).

fof(f154,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f206,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_7
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_7
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f78,f83,f149,f195,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f42,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f195,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f149,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f83,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f196,plain,
    ( ~ spl4_11
    | spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f189,f160,f182,f193])).

fof(f160,plain,
    ( spl4_9
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f189,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f162,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f162,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f186,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f185,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f175,f152,f182])).

fof(f175,plain,
    ( sK0 = sK1
    | ~ spl4_8 ),
    inference(resolution,[],[f153,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f153,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f174,plain,
    ( ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f141,f148,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f148,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f141,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f169,plain,
    ( ~ spl4_3
    | spl4_7
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl4_3
    | spl4_7
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f149,f154,f87,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f87,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f163,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f143,f90,f160,f81,f76])).

fof(f90,plain,
    ( spl4_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f143,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f91,f40])).

fof(f91,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f155,plain,
    ( ~ spl4_8
    | spl4_3 ),
    inference(avatar_split_clause,[],[f145,f86,f152])).

fof(f145,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl4_3 ),
    inference(resolution,[],[f88,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f150,plain,
    ( ~ spl4_7
    | spl4_3 ),
    inference(avatar_split_clause,[],[f144,f86,f147])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3 ),
    inference(resolution,[],[f88,f67])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f142,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f135,f90,f139,f81,f76])).

fof(f135,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_4 ),
    inference(resolution,[],[f42,f92])).

fof(f92,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f94,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f62,f90,f86])).

fof(f62,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f57,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f38,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f93,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f61,f90,f86])).

fof(f61,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f39,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f36,f76])).

fof(f36,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:31:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.47  % (5740)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (5757)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.47  % (5749)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.48  % (5751)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.48  % (5734)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.48  % (5738)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.49  % (5741)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.49  % (5756)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.49  % (5742)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.49  % (5758)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.49  % (5757)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f79,f84,f93,f94,f142,f150,f155,f163,f169,f174,f185,f186,f196,f206,f234,f239])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    spl4_14),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f235])).
% 0.20/0.49  fof(f235,plain,(
% 0.20/0.49    $false | spl4_14),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f71,f233])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k1_tarski(sK0)) | spl4_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f231])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    spl4_14 <=> r2_hidden(sK0,k1_tarski(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.49    inference(equality_resolution,[],[f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.49    inference(equality_resolution,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.49    inference(rectify,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    ~spl4_14 | spl4_8 | ~spl4_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f213,f182,f152,f231])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl4_8 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    spl4_10 <=> sK0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k1_tarski(sK0)) | (spl4_8 | ~spl4_10)),
% 0.20/0.49    inference(superposition,[],[f154,f184])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    sK0 = sK1 | ~spl4_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f182])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k1_tarski(sK1)) | spl4_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f152])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2 | spl4_7 | spl4_11),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f201])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    $false | (~spl4_1 | ~spl4_2 | spl4_7 | spl4_11)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f78,f83,f149,f195,f137])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.20/0.49    inference(resolution,[],[f42,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~r1_tarski(sK1,sK0) | spl4_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f193])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    spl4_11 <=> r1_tarski(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK1) | spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    spl4_7 <=> r2_hidden(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    v3_ordinal1(sK1) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl4_2 <=> v3_ordinal1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    v3_ordinal1(sK0) | ~spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl4_1 <=> v3_ordinal1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ~spl4_11 | spl4_10 | ~spl4_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f189,f160,f182,f193])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl4_9 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl4_9),
% 0.20/0.49    inference(resolution,[],[f162,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~spl4_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f160])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    sK0 != sK1 | r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    spl4_10 | ~spl4_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f175,f152,f182])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    sK0 = sK1 | ~spl4_8),
% 0.20/0.49    inference(resolution,[],[f153,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.49    inference(equality_resolution,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    r2_hidden(sK0,k1_tarski(sK1)) | ~spl4_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f152])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~spl4_6 | ~spl4_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f171])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    $false | (~spl4_6 | ~spl4_7)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f141,f148,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    r2_hidden(sK0,sK1) | ~spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f147])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    r2_hidden(sK1,sK0) | ~spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f139])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl4_6 <=> r2_hidden(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ~spl4_3 | spl4_7 | spl4_8),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    $false | (~spl4_3 | spl4_7 | spl4_8)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f149,f154,f87,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(rectify,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl4_3 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2 | spl4_9 | ~spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f143,f90,f160,f81,f76])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl4_4 <=> r1_ordinal1(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl4_4),
% 0.20/0.49    inference(resolution,[],[f91,f40])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    r1_ordinal1(sK0,sK1) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    ~spl4_8 | spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f145,f86,f152])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k1_tarski(sK1)) | spl4_3),
% 0.20/0.49    inference(resolution,[],[f88,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f86])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ~spl4_7 | spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f144,f86,f147])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK1) | spl4_3),
% 0.20/0.49    inference(resolution,[],[f88,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2 | spl4_6 | spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f135,f90,f139,f81,f76])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_4),
% 0.20/0.49    inference(resolution,[],[f42,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ~r1_ordinal1(sK0,sK1) | spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl4_3 | spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f62,f90,f86])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.20/0.49    inference(definition_unfolding,[],[f38,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ~spl4_3 | ~spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f61,f90,f86])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.20/0.49    inference(definition_unfolding,[],[f39,f57])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f81])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    v3_ordinal1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f76])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v3_ordinal1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (5757)------------------------------
% 0.20/0.49  % (5757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5757)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (5757)Memory used [KB]: 10874
% 0.20/0.49  % (5757)Time elapsed: 0.069 s
% 0.20/0.49  % (5757)------------------------------
% 0.20/0.49  % (5757)------------------------------
% 0.20/0.49  % (5736)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.49  % (5739)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (5733)Success in time 0.152 s
%------------------------------------------------------------------------------
