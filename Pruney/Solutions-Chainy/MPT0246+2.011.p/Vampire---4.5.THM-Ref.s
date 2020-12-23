%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 286 expanded)
%              Number of leaves         :   30 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  314 ( 788 expanded)
%              Number of equality atoms :  104 ( 291 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f519,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f90,f99,f112,f146,f163,f184,f197,f226,f283,f308,f318,f389,f416,f439,f517,f518])).

fof(f518,plain,
    ( sK1 != sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != sK2(sK0)
    | r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f517,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f516])).

fof(f516,plain,
    ( $false
    | spl4_27 ),
    inference(subsumption_resolution,[],[f510,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f510,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_27 ),
    inference(unit_resulting_resolution,[],[f435,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f435,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl4_27
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f439,plain,
    ( ~ spl4_27
    | ~ spl4_10
    | spl4_26 ),
    inference(avatar_split_clause,[],[f438,f413,f177,f433])).

fof(f177,plain,
    ( spl4_10
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f413,plain,
    ( spl4_26
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f438,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_10
    | spl4_26 ),
    inference(forward_demodulation,[],[f428,f179])).

fof(f179,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f428,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)
    | spl4_26 ),
    inference(resolution,[],[f415,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f415,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f413])).

fof(f416,plain,
    ( ~ spl4_26
    | spl4_19
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f411,f343,f305,f413])).

fof(f305,plain,
    ( spl4_19
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f343,plain,
    ( spl4_22
  <=> sK1 = sK3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f411,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl4_19
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f410,f307])).

fof(f307,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f305])).

fof(f410,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_22 ),
    inference(superposition,[],[f37,f345])).

fof(f345,plain,
    ( sK1 = sK3(sK0,k1_xboole_0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f343])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f389,plain,
    ( spl4_22
    | spl4_1
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f388,f315,f51,f343])).

fof(f51,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f315,plain,
    ( spl4_21
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f388,plain,
    ( sK1 = sK3(sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f386,f53])).

fof(f53,plain,
    ( k1_xboole_0 != sK0
    | spl4_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f386,plain,
    ( sK1 = sK3(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f383])).

fof(f383,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = sK3(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl4_21 ),
    inference(superposition,[],[f218,f317])).

fof(f317,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f315])).

fof(f218,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(X0,sK0)
      | sK1 = sK3(sK0,X0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f123,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f123,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK0)
      | sK0 = X4
      | sK1 = sK3(sK0,X4) ) ),
    inference(resolution,[],[f80,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK1 = sK3(sK0,X0) ) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & sK0 != k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f318,plain,
    ( spl4_21
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f294,f177,f108,f315])).

fof(f108,plain,
    ( spl4_7
  <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f294,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f110,f179])).

fof(f110,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f308,plain,
    ( ~ spl4_19
    | spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f292,f177,f155,f305])).

fof(f155,plain,
    ( spl4_9
  <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f292,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl4_9
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f157,f179])).

fof(f157,plain,
    ( ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f283,plain,
    ( spl4_10
    | spl4_17
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f278,f181,f280,f177])).

fof(f280,plain,
    ( spl4_17
  <=> r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f181,plain,
    ( spl4_11
  <=> sK1 = sK2(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f278,plain,
    ( r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl4_11 ),
    inference(superposition,[],[f30,f183])).

fof(f183,plain,
    ( sK1 = sK2(k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f226,plain,
    ( spl4_15
    | spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f225,f143,f56,f209])).

fof(f209,plain,
    ( spl4_15
  <=> sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f56,plain,
    ( spl4_2
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f143,plain,
    ( spl4_8
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f225,plain,
    ( sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f222,f58])).

fof(f58,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f222,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f123,f145])).

fof(f145,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f197,plain,
    ( ~ spl4_12
    | spl4_9 ),
    inference(avatar_split_clause,[],[f188,f155,f194])).

fof(f194,plain,
    ( spl4_12
  <=> r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f188,plain,
    ( ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f157,f37])).

fof(f184,plain,
    ( spl4_10
    | spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f175,f143,f181,f177])).

fof(f175,plain,
    ( sK1 = sK2(k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f128,f145])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK1 = sK2(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f82,f30])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | sK1 = X2
      | ~ r1_tarski(X3,sK0) ) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f163,plain,
    ( ~ spl4_9
    | spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f162,f143,f56,f155])).

fof(f162,plain,
    ( ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f153,f58])).

fof(f153,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f145,f34])).

fof(f146,plain,
    ( spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f138,f108,f143])).

fof(f138,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f110,f38])).

fof(f112,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f105,f94,f108])).

fof(f94,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f105,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f96,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f99,plain,
    ( spl4_6
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f98,f84,f51,f94])).

fof(f84,plain,
    ( spl4_5
  <=> sK1 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f98,plain,
    ( r2_hidden(sK1,sK0)
    | spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f92,f53])).

fof(f92,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(superposition,[],[f30,f86])).

fof(f86,plain,
    ( sK1 = sK2(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f90,plain,
    ( spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f89,f51,f84])).

fof(f89,plain,
    ( sK1 = sK2(sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f79,f53])).

fof(f79,plain,
    ( sK1 = sK2(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f28,f30])).

fof(f59,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f45,f56])).

fof(f45,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f26,f44])).

fof(f26,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:58:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.51  % (28421)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (28429)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (28413)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (28404)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (28404)Refutation not found, incomplete strategy% (28404)------------------------------
% 0.21/0.52  % (28404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28404)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28404)Memory used [KB]: 1663
% 0.21/0.52  % (28404)Time elapsed: 0.104 s
% 0.21/0.52  % (28404)------------------------------
% 0.21/0.52  % (28404)------------------------------
% 0.21/0.52  % (28421)Refutation not found, incomplete strategy% (28421)------------------------------
% 0.21/0.52  % (28421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28405)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (28413)Refutation not found, incomplete strategy% (28413)------------------------------
% 0.21/0.52  % (28413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28413)Memory used [KB]: 10618
% 0.21/0.52  % (28413)Time elapsed: 0.108 s
% 0.21/0.52  % (28413)------------------------------
% 0.21/0.52  % (28413)------------------------------
% 0.21/0.52  % (28421)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28421)Memory used [KB]: 10618
% 0.21/0.52  % (28421)Time elapsed: 0.108 s
% 0.21/0.52  % (28421)------------------------------
% 0.21/0.52  % (28421)------------------------------
% 0.21/0.53  % (28409)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (28416)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (28415)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (28418)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (28410)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (28429)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (28425)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (28427)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (28412)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (28408)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28417)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (28430)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (28420)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (28419)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (28433)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (28407)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (28426)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (28428)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (28415)Refutation not found, incomplete strategy% (28415)------------------------------
% 0.21/0.55  % (28415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28415)Memory used [KB]: 10618
% 0.21/0.55  % (28415)Time elapsed: 0.127 s
% 0.21/0.55  % (28415)------------------------------
% 0.21/0.55  % (28415)------------------------------
% 0.21/0.55  % (28411)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (28431)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (28424)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (28423)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f519,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(avatar_sat_refutation,[],[f54,f59,f90,f99,f112,f146,f163,f184,f197,f226,f283,f308,f318,f389,f416,f439,f517,f518])).
% 1.40/0.55  fof(f518,plain,(
% 1.40/0.55    sK1 != sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 != sK2(sK0) | r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.40/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.40/0.55  fof(f517,plain,(
% 1.40/0.55    spl4_27),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f516])).
% 1.40/0.55  fof(f516,plain,(
% 1.40/0.55    $false | spl4_27),
% 1.40/0.55    inference(subsumption_resolution,[],[f510,f49])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.40/0.55    inference(equality_resolution,[],[f32])).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(flattening,[],[f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.55  fof(f510,plain,(
% 1.40/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_27),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f435,f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f24])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.40/0.55    inference(nnf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.40/0.55  fof(f435,plain,(
% 1.40/0.55    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | spl4_27),
% 1.40/0.55    inference(avatar_component_clause,[],[f433])).
% 1.40/0.55  fof(f433,plain,(
% 1.40/0.55    spl4_27 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.40/0.55  fof(f439,plain,(
% 1.40/0.55    ~spl4_27 | ~spl4_10 | spl4_26),
% 1.40/0.55    inference(avatar_split_clause,[],[f438,f413,f177,f433])).
% 1.40/0.55  fof(f177,plain,(
% 1.40/0.55    spl4_10 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.40/0.55  fof(f413,plain,(
% 1.40/0.55    spl4_26 <=> r2_hidden(sK1,k1_xboole_0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.40/0.55  fof(f438,plain,(
% 1.40/0.55    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_10 | spl4_26)),
% 1.40/0.55    inference(forward_demodulation,[],[f428,f179])).
% 1.40/0.55  fof(f179,plain,(
% 1.40/0.55    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl4_10),
% 1.40/0.55    inference(avatar_component_clause,[],[f177])).
% 1.40/0.55  fof(f428,plain,(
% 1.40/0.55    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) | spl4_26),
% 1.40/0.55    inference(resolution,[],[f415,f47])).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f40,f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f29,f43])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f31,f42])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.55  fof(f40,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f25])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.40/0.55    inference(nnf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.40/0.55  fof(f415,plain,(
% 1.40/0.55    ~r2_hidden(sK1,k1_xboole_0) | spl4_26),
% 1.40/0.55    inference(avatar_component_clause,[],[f413])).
% 1.40/0.55  fof(f416,plain,(
% 1.40/0.55    ~spl4_26 | spl4_19 | ~spl4_22),
% 1.40/0.55    inference(avatar_split_clause,[],[f411,f343,f305,f413])).
% 1.40/0.55  fof(f305,plain,(
% 1.40/0.55    spl4_19 <=> r1_tarski(sK0,k1_xboole_0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.40/0.55  fof(f343,plain,(
% 1.40/0.55    spl4_22 <=> sK1 = sK3(sK0,k1_xboole_0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.40/0.55  fof(f411,plain,(
% 1.40/0.55    ~r2_hidden(sK1,k1_xboole_0) | (spl4_19 | ~spl4_22)),
% 1.40/0.55    inference(subsumption_resolution,[],[f410,f307])).
% 1.40/0.55  fof(f307,plain,(
% 1.40/0.55    ~r1_tarski(sK0,k1_xboole_0) | spl4_19),
% 1.40/0.55    inference(avatar_component_clause,[],[f305])).
% 1.40/0.55  fof(f410,plain,(
% 1.40/0.55    ~r2_hidden(sK1,k1_xboole_0) | r1_tarski(sK0,k1_xboole_0) | ~spl4_22),
% 1.40/0.55    inference(superposition,[],[f37,f345])).
% 1.40/0.55  fof(f345,plain,(
% 1.40/0.55    sK1 = sK3(sK0,k1_xboole_0) | ~spl4_22),
% 1.40/0.55    inference(avatar_component_clause,[],[f343])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f23])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.55    inference(rectify,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.55    inference(nnf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,plain,(
% 1.40/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.55  fof(f389,plain,(
% 1.40/0.55    spl4_22 | spl4_1 | ~spl4_21),
% 1.40/0.55    inference(avatar_split_clause,[],[f388,f315,f51,f343])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    spl4_1 <=> k1_xboole_0 = sK0),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.40/0.55  fof(f315,plain,(
% 1.40/0.55    spl4_21 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.40/0.55  fof(f388,plain,(
% 1.40/0.55    sK1 = sK3(sK0,k1_xboole_0) | (spl4_1 | ~spl4_21)),
% 1.40/0.55    inference(subsumption_resolution,[],[f386,f53])).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    k1_xboole_0 != sK0 | spl4_1),
% 1.40/0.55    inference(avatar_component_clause,[],[f51])).
% 1.40/0.55  fof(f386,plain,(
% 1.40/0.55    sK1 = sK3(sK0,k1_xboole_0) | k1_xboole_0 = sK0 | ~spl4_21),
% 1.40/0.55    inference(trivial_inequality_removal,[],[f383])).
% 1.40/0.55  fof(f383,plain,(
% 1.40/0.55    k1_xboole_0 != k1_xboole_0 | sK1 = sK3(sK0,k1_xboole_0) | k1_xboole_0 = sK0 | ~spl4_21),
% 1.40/0.55    inference(superposition,[],[f218,f317])).
% 1.40/0.55  fof(f317,plain,(
% 1.40/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | ~spl4_21),
% 1.40/0.55    inference(avatar_component_clause,[],[f315])).
% 1.40/0.55  fof(f218,plain,(
% 1.40/0.55    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,sK0) | sK1 = sK3(sK0,X0) | sK0 = X0) )),
% 1.40/0.55    inference(resolution,[],[f123,f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f24])).
% 1.40/0.55  fof(f123,plain,(
% 1.40/0.55    ( ! [X4] : (~r1_tarski(X4,sK0) | sK0 = X4 | sK1 = sK3(sK0,X4)) )),
% 1.40/0.55    inference(resolution,[],[f80,f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f19])).
% 1.40/0.55  fof(f80,plain,(
% 1.40/0.55    ( ! [X0] : (r1_tarski(sK0,X0) | sK1 = sK3(sK0,X0)) )),
% 1.40/0.55    inference(resolution,[],[f28,f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f23])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 1.40/0.55    inference(cnf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,plain,(
% 1.40/0.55    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).
% 1.40/0.55  fof(f14,plain,(
% 1.40/0.55    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f11,plain,(
% 1.40/0.55    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.40/0.55    inference(ennf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.40/0.55    inference(negated_conjecture,[],[f9])).
% 1.40/0.55  fof(f9,conjecture,(
% 1.40/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.40/0.55  fof(f318,plain,(
% 1.40/0.55    spl4_21 | ~spl4_7 | ~spl4_10),
% 1.40/0.55    inference(avatar_split_clause,[],[f294,f177,f108,f315])).
% 1.40/0.55  fof(f108,plain,(
% 1.40/0.55    spl4_7 <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.40/0.55  fof(f294,plain,(
% 1.40/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | (~spl4_7 | ~spl4_10)),
% 1.40/0.55    inference(backward_demodulation,[],[f110,f179])).
% 1.40/0.55  fof(f110,plain,(
% 1.40/0.55    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl4_7),
% 1.40/0.55    inference(avatar_component_clause,[],[f108])).
% 1.40/0.55  fof(f308,plain,(
% 1.40/0.55    ~spl4_19 | spl4_9 | ~spl4_10),
% 1.40/0.55    inference(avatar_split_clause,[],[f292,f177,f155,f305])).
% 1.40/0.55  fof(f155,plain,(
% 1.40/0.55    spl4_9 <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.40/0.55  fof(f292,plain,(
% 1.40/0.55    ~r1_tarski(sK0,k1_xboole_0) | (spl4_9 | ~spl4_10)),
% 1.40/0.55    inference(backward_demodulation,[],[f157,f179])).
% 1.40/0.55  fof(f157,plain,(
% 1.40/0.55    ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_9),
% 1.40/0.55    inference(avatar_component_clause,[],[f155])).
% 1.40/0.55  fof(f283,plain,(
% 1.40/0.55    spl4_10 | spl4_17 | ~spl4_11),
% 1.40/0.55    inference(avatar_split_clause,[],[f278,f181,f280,f177])).
% 1.40/0.55  fof(f280,plain,(
% 1.40/0.55    spl4_17 <=> r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.40/0.55  fof(f181,plain,(
% 1.40/0.55    spl4_11 <=> sK1 = sK2(k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.40/0.55  fof(f278,plain,(
% 1.40/0.55    r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl4_11),
% 1.40/0.55    inference(superposition,[],[f30,f183])).
% 1.40/0.55  fof(f183,plain,(
% 1.40/0.55    sK1 = sK2(k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_11),
% 1.40/0.55    inference(avatar_component_clause,[],[f181])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f17])).
% 1.40/0.55  fof(f17,plain,(
% 1.40/0.55    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f16])).
% 1.40/0.56  fof(f16,plain,(
% 1.40/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f12,plain,(
% 1.40/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.40/0.56    inference(ennf_transformation,[],[f2])).
% 1.40/0.56  fof(f2,axiom,(
% 1.40/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.40/0.56  fof(f226,plain,(
% 1.40/0.56    spl4_15 | spl4_2 | ~spl4_8),
% 1.40/0.56    inference(avatar_split_clause,[],[f225,f143,f56,f209])).
% 1.40/0.56  fof(f209,plain,(
% 1.40/0.56    spl4_15 <=> sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.40/0.56  fof(f56,plain,(
% 1.40/0.56    spl4_2 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.40/0.56  fof(f143,plain,(
% 1.40/0.56    spl4_8 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.40/0.56  fof(f225,plain,(
% 1.40/0.56    sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl4_2 | ~spl4_8)),
% 1.40/0.56    inference(subsumption_resolution,[],[f222,f58])).
% 1.40/0.56  fof(f58,plain,(
% 1.40/0.56    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | spl4_2),
% 1.40/0.56    inference(avatar_component_clause,[],[f56])).
% 1.40/0.56  fof(f222,plain,(
% 1.40/0.56    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_8),
% 1.40/0.56    inference(resolution,[],[f123,f145])).
% 1.40/0.56  fof(f145,plain,(
% 1.40/0.56    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl4_8),
% 1.40/0.56    inference(avatar_component_clause,[],[f143])).
% 1.40/0.56  fof(f197,plain,(
% 1.40/0.56    ~spl4_12 | spl4_9),
% 1.40/0.56    inference(avatar_split_clause,[],[f188,f155,f194])).
% 1.40/0.56  fof(f194,plain,(
% 1.40/0.56    spl4_12 <=> r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.40/0.56  fof(f188,plain,(
% 1.40/0.56    ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_9),
% 1.40/0.56    inference(unit_resulting_resolution,[],[f157,f37])).
% 1.40/0.56  fof(f184,plain,(
% 1.40/0.56    spl4_10 | spl4_11 | ~spl4_8),
% 1.40/0.56    inference(avatar_split_clause,[],[f175,f143,f181,f177])).
% 1.40/0.56  fof(f175,plain,(
% 1.40/0.56    sK1 = sK2(k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl4_8),
% 1.40/0.56    inference(resolution,[],[f128,f145])).
% 1.40/0.56  fof(f128,plain,(
% 1.40/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | sK1 = sK2(X0) | k1_xboole_0 = X0) )),
% 1.40/0.56    inference(resolution,[],[f82,f30])).
% 1.40/0.56  fof(f82,plain,(
% 1.40/0.56    ( ! [X2,X3] : (~r2_hidden(X2,X3) | sK1 = X2 | ~r1_tarski(X3,sK0)) )),
% 1.40/0.56    inference(resolution,[],[f28,f35])).
% 1.40/0.56  fof(f35,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f23])).
% 1.40/0.56  fof(f163,plain,(
% 1.40/0.56    ~spl4_9 | spl4_2 | ~spl4_8),
% 1.40/0.56    inference(avatar_split_clause,[],[f162,f143,f56,f155])).
% 1.40/0.56  fof(f162,plain,(
% 1.40/0.56    ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl4_2 | ~spl4_8)),
% 1.40/0.56    inference(subsumption_resolution,[],[f153,f58])).
% 1.40/0.56  fof(f153,plain,(
% 1.40/0.56    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_8),
% 1.40/0.56    inference(resolution,[],[f145,f34])).
% 1.40/0.56  fof(f146,plain,(
% 1.40/0.56    spl4_8 | ~spl4_7),
% 1.40/0.56    inference(avatar_split_clause,[],[f138,f108,f143])).
% 1.40/0.56  fof(f138,plain,(
% 1.40/0.56    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl4_7),
% 1.40/0.56    inference(unit_resulting_resolution,[],[f110,f38])).
% 1.40/0.56  fof(f112,plain,(
% 1.40/0.56    spl4_7 | ~spl4_6),
% 1.40/0.56    inference(avatar_split_clause,[],[f105,f94,f108])).
% 1.40/0.56  fof(f94,plain,(
% 1.40/0.56    spl4_6 <=> r2_hidden(sK1,sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.40/0.56  fof(f105,plain,(
% 1.40/0.56    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl4_6),
% 1.40/0.56    inference(resolution,[],[f96,f46])).
% 1.40/0.56  fof(f46,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.40/0.56    inference(definition_unfolding,[],[f41,f44])).
% 1.40/0.56  fof(f41,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f25])).
% 1.40/0.56  fof(f96,plain,(
% 1.40/0.56    r2_hidden(sK1,sK0) | ~spl4_6),
% 1.40/0.56    inference(avatar_component_clause,[],[f94])).
% 1.40/0.56  fof(f99,plain,(
% 1.40/0.56    spl4_6 | spl4_1 | ~spl4_5),
% 1.40/0.56    inference(avatar_split_clause,[],[f98,f84,f51,f94])).
% 1.40/0.56  fof(f84,plain,(
% 1.40/0.56    spl4_5 <=> sK1 = sK2(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.40/0.56  fof(f98,plain,(
% 1.40/0.56    r2_hidden(sK1,sK0) | (spl4_1 | ~spl4_5)),
% 1.40/0.56    inference(subsumption_resolution,[],[f92,f53])).
% 1.40/0.56  fof(f92,plain,(
% 1.40/0.56    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0 | ~spl4_5),
% 1.40/0.56    inference(superposition,[],[f30,f86])).
% 1.40/0.56  fof(f86,plain,(
% 1.40/0.56    sK1 = sK2(sK0) | ~spl4_5),
% 1.40/0.56    inference(avatar_component_clause,[],[f84])).
% 1.40/0.56  fof(f90,plain,(
% 1.40/0.56    spl4_5 | spl4_1),
% 1.40/0.56    inference(avatar_split_clause,[],[f89,f51,f84])).
% 1.40/0.56  fof(f89,plain,(
% 1.40/0.56    sK1 = sK2(sK0) | spl4_1),
% 1.40/0.56    inference(subsumption_resolution,[],[f79,f53])).
% 1.40/0.56  fof(f79,plain,(
% 1.40/0.56    sK1 = sK2(sK0) | k1_xboole_0 = sK0),
% 1.40/0.56    inference(resolution,[],[f28,f30])).
% 1.40/0.56  fof(f59,plain,(
% 1.40/0.56    ~spl4_2),
% 1.40/0.56    inference(avatar_split_clause,[],[f45,f56])).
% 1.40/0.56  fof(f45,plain,(
% 1.40/0.56    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.40/0.56    inference(definition_unfolding,[],[f26,f44])).
% 1.40/0.56  fof(f26,plain,(
% 1.40/0.56    sK0 != k1_tarski(sK1)),
% 1.40/0.56    inference(cnf_transformation,[],[f15])).
% 1.40/0.56  fof(f54,plain,(
% 1.40/0.56    ~spl4_1),
% 1.40/0.56    inference(avatar_split_clause,[],[f27,f51])).
% 1.40/0.56  fof(f27,plain,(
% 1.40/0.56    k1_xboole_0 != sK0),
% 1.40/0.56    inference(cnf_transformation,[],[f15])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (28429)------------------------------
% 1.40/0.56  % (28429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (28429)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (28429)Memory used [KB]: 6396
% 1.40/0.56  % (28429)Time elapsed: 0.119 s
% 1.40/0.56  % (28429)------------------------------
% 1.40/0.56  % (28429)------------------------------
% 1.40/0.56  % (28403)Success in time 0.185 s
%------------------------------------------------------------------------------
