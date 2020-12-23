%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 138 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 ( 429 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f696,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f78,f98,f108,f138,f166,f553,f695])).

fof(f695,plain,
    ( ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f694])).

fof(f694,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f688,f107])).

fof(f107,plain,
    ( r2_hidden(sK6(sK7(sK3),sK3),sK7(sK3))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_7
  <=> r2_hidden(sK6(sK7(sK3),sK3),sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f688,plain,
    ( ~ r2_hidden(sK6(sK7(sK3),sK3),sK7(sK3))
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f148,f137,f60])).

fof(f60,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK7(X1))
      | ~ r2_hidden(X3,X1)
      | ~ sP8(X1) ) ),
    inference(general_splitting,[],[f57,f59_D])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sP8(X1) ) ),
    inference(cnf_transformation,[],[f59_D])).

fof(f59_D,plain,(
    ! [X1] :
      ( ! [X0] : ~ r2_hidden(X0,X1)
    <=> ~ sP8(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK7(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f34])).

fof(f34,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f137,plain,
    ( r2_hidden(sK6(sK7(sK3),sK3),sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl9_11
  <=> r2_hidden(sK6(sK7(sK3),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f148,plain,
    ( sP8(sK3)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl9_12
  <=> sP8(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f553,plain,
    ( spl9_1
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f462,f334])).

fof(f334,plain,
    ( ! [X0,X1] : ~ sP0(X0,k1_xboole_0,X1)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f85,f190,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X0,X4)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,X0,sK4(X0,X1,X2))
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sP0(X1,X0,sK4(X0,X1,X2))
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,X0,sK4(X0,X1,X2))
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sP0(X1,X0,sK4(X0,X1,X2))
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X0,X3) )
            & ( sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f190,plain,
    ( ! [X0] : sP1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f188,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f188,plain,
    ( ! [X0] : sP1(k1_xboole_0,X0,k10_relat_1(k1_xboole_0,X0))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f77,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,k10_relat_1(X0,X1))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ~ sP1(X0,X1,X2) )
          & ( sP1(X0,X1,X2)
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> sP1(X0,X1,X2) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f77,plain,
    ( sP2(k1_xboole_0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl9_3
  <=> sP2(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f85,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f40,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f462,plain,
    ( ! [X0] : sP0(X0,k1_xboole_0,sK4(k1_xboole_0,X0,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f274,f97,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,sK4(X0,X1,X2))
      | sP1(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_6
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f274,plain,
    ( ! [X0] : ~ sP1(k1_xboole_0,X0,sK3)
    | spl9_1
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f64,f273])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ sP1(k1_xboole_0,X0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f266,f77])).

fof(f266,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP1(k1_xboole_0,X0,X1)
      | ~ sP2(k1_xboole_0) ) ),
    inference(superposition,[],[f43,f41])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ sP1(X0,X1,X2)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,
    ( k1_xboole_0 != sK3
    | spl9_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl9_1
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f166,plain,
    ( spl9_12
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f144,f135,f146])).

fof(f144,plain,
    ( sP8(sK3)
    | ~ spl9_11 ),
    inference(resolution,[],[f137,f59])).

fof(f138,plain,
    ( spl9_11
    | spl9_5 ),
    inference(avatar_split_clause,[],[f129,f92,f135])).

fof(f92,plain,
    ( spl9_5
  <=> r1_xboole_0(sK7(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f129,plain,
    ( r2_hidden(sK6(sK7(sK3),sK3),sK3)
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f94,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f94,plain,
    ( ~ r1_xboole_0(sK7(sK3),sK3)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f108,plain,
    ( spl9_7
    | spl9_5 ),
    inference(avatar_split_clause,[],[f99,f92,f105])).

fof(f99,plain,
    ( r2_hidden(sK6(sK7(sK3),sK3),sK7(sK3))
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f94,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,
    ( ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f88,f96,f92])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r1_xboole_0(sK7(sK3),sK3) ) ),
    inference(resolution,[],[f56,f37])).

fof(f37,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ r1_xboole_0(X1,sK3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK3)
        | ~ r2_hidden(X1,sK3) )
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK3)
          | ~ r2_hidden(X1,sK3) )
      & k1_xboole_0 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f72,f67,f75])).

fof(f67,plain,
    ( spl9_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f72,plain,
    ( sP2(k1_xboole_0)
    | ~ spl9_2 ),
    inference(superposition,[],[f71,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f71,plain,(
    ! [X0] : sP2(k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f39,f51])).

fof(f51,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f13,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0,X3] :
      ( sP0(X1,X0,X3)
    <=> ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X3,X4),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f70,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f65,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (1936)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.46  % (1936)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f696,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f65,f70,f78,f98,f108,f138,f166,f553,f695])).
% 0.22/0.46  fof(f695,plain,(
% 0.22/0.46    ~spl9_7 | ~spl9_11 | ~spl9_12),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f694])).
% 0.22/0.46  fof(f694,plain,(
% 0.22/0.46    $false | (~spl9_7 | ~spl9_11 | ~spl9_12)),
% 0.22/0.46    inference(subsumption_resolution,[],[f688,f107])).
% 0.22/0.46  fof(f107,plain,(
% 0.22/0.46    r2_hidden(sK6(sK7(sK3),sK3),sK7(sK3)) | ~spl9_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f105])).
% 0.22/0.46  fof(f105,plain,(
% 0.22/0.46    spl9_7 <=> r2_hidden(sK6(sK7(sK3),sK3),sK7(sK3))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.46  fof(f688,plain,(
% 0.22/0.46    ~r2_hidden(sK6(sK7(sK3),sK3),sK7(sK3)) | (~spl9_11 | ~spl9_12)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f148,f137,f60])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ( ! [X3,X1] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1) | ~sP8(X1)) )),
% 0.22/0.46    inference(general_splitting,[],[f57,f59_D])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sP8(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f59_D])).
% 0.22/0.46  fof(f59_D,plain,(
% 0.22/0.46    ( ! [X1] : (( ! [X0] : ~r2_hidden(X0,X1) ) <=> ~sP8(X1)) )),
% 0.22/0.46    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK7(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK7(X1),X1)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.46  fof(f137,plain,(
% 0.22/0.46    r2_hidden(sK6(sK7(sK3),sK3),sK3) | ~spl9_11),
% 0.22/0.46    inference(avatar_component_clause,[],[f135])).
% 0.22/0.46  fof(f135,plain,(
% 0.22/0.46    spl9_11 <=> r2_hidden(sK6(sK7(sK3),sK3),sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.46  fof(f148,plain,(
% 0.22/0.46    sP8(sK3) | ~spl9_12),
% 0.22/0.46    inference(avatar_component_clause,[],[f146])).
% 0.22/0.46  fof(f146,plain,(
% 0.22/0.46    spl9_12 <=> sP8(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.46  fof(f553,plain,(
% 0.22/0.46    spl9_1 | ~spl9_3 | ~spl9_6),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f552])).
% 0.22/0.46  fof(f552,plain,(
% 0.22/0.46    $false | (spl9_1 | ~spl9_3 | ~spl9_6)),
% 0.22/0.46    inference(subsumption_resolution,[],[f462,f334])).
% 0.22/0.46  fof(f334,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~sP0(X0,k1_xboole_0,X1)) ) | ~spl9_3),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f85,f190,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X0,X4) | r2_hidden(X4,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,X0,sK4(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sP0(X1,X0,sK4(X0,X1,X2)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X0,X4)) & (sP0(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2))) => ((~sP0(X1,X0,sK4(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sP0(X1,X0,sK4(X0,X1,X2)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X0,X4)) & (sP0(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.46    inference(rectify,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X0,X3)) & (sP0(X1,X0,X3) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.46    inference(nnf_transformation,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X0,X3)))),
% 0.22/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.46  fof(f190,plain,(
% 0.22/0.46    ( ! [X0] : (sP1(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl9_3),
% 0.22/0.46    inference(forward_demodulation,[],[f188,f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.46  fof(f188,plain,(
% 0.22/0.46    ( ! [X0] : (sP1(k1_xboole_0,X0,k10_relat_1(k1_xboole_0,X0))) ) | ~spl9_3),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f77,f58])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    ( ! [X0,X1] : (sP1(X0,X1,k10_relat_1(X0,X1)) | ~sP2(X0)) )),
% 0.22/0.46    inference(equality_resolution,[],[f42])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k10_relat_1(X0,X1) != X2 | ~sP2(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k10_relat_1(X0,X1) != X2)) | ~sP2(X0))),
% 0.22/0.46    inference(nnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> sP1(X0,X1,X2)) | ~sP2(X0))),
% 0.22/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    sP2(k1_xboole_0) | ~spl9_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f75])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    spl9_3 <=> sP2(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f40,f55])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.46  fof(f462,plain,(
% 0.22/0.46    ( ! [X0] : (sP0(X0,k1_xboole_0,sK4(k1_xboole_0,X0,sK3))) ) | (spl9_1 | ~spl9_3 | ~spl9_6)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f274,f97,f46])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (sP0(X1,X0,sK4(X0,X1,X2)) | sP1(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl9_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f96])).
% 0.22/0.46  fof(f96,plain,(
% 0.22/0.46    spl9_6 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.46  fof(f274,plain,(
% 0.22/0.46    ( ! [X0] : (~sP1(k1_xboole_0,X0,sK3)) ) | (spl9_1 | ~spl9_3)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f64,f273])).
% 0.22/0.46  fof(f273,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~sP1(k1_xboole_0,X0,X1) | k1_xboole_0 = X1) ) | ~spl9_3),
% 0.22/0.46    inference(subsumption_resolution,[],[f266,f77])).
% 0.22/0.46  fof(f266,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP1(k1_xboole_0,X0,X1) | ~sP2(k1_xboole_0)) )),
% 0.22/0.46    inference(superposition,[],[f43,f41])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | ~sP1(X0,X1,X2) | ~sP2(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    k1_xboole_0 != sK3 | spl9_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f62])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    spl9_1 <=> k1_xboole_0 = sK3),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.46  fof(f166,plain,(
% 0.22/0.46    spl9_12 | ~spl9_11),
% 0.22/0.46    inference(avatar_split_clause,[],[f144,f135,f146])).
% 0.22/0.46  fof(f144,plain,(
% 0.22/0.46    sP8(sK3) | ~spl9_11),
% 0.22/0.46    inference(resolution,[],[f137,f59])).
% 0.22/0.46  fof(f138,plain,(
% 0.22/0.46    spl9_11 | spl9_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f129,f92,f135])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    spl9_5 <=> r1_xboole_0(sK7(sK3),sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.46  fof(f129,plain,(
% 0.22/0.46    r2_hidden(sK6(sK7(sK3),sK3),sK3) | spl9_5),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f94,f53])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(ennf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(rectify,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    ~r1_xboole_0(sK7(sK3),sK3) | spl9_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f92])).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    spl9_7 | spl9_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f99,f92,f105])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    r2_hidden(sK6(sK7(sK3),sK3),sK7(sK3)) | spl9_5),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f94,f52])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f33])).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    ~spl9_5 | spl9_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f88,f96,f92])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r1_xboole_0(sK7(sK3),sK3)) )),
% 0.22/0.46    inference(resolution,[],[f56,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X1] : (~r2_hidden(X1,sK3) | ~r1_xboole_0(X1,sK3)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ! [X1] : (~r1_xboole_0(X1,sK3) | ~r2_hidden(X1,sK3)) & k1_xboole_0 != sK3),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK3) | ~r2_hidden(X1,sK3)) & k1_xboole_0 != sK3)),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,negated_conjecture,(
% 0.22/0.46    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.46    inference(negated_conjecture,[],[f9])).
% 0.22/0.46  fof(f9,conjecture,(
% 0.22/0.46    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(sK7(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f35])).
% 0.22/0.46  fof(f78,plain,(
% 0.22/0.46    spl9_3 | ~spl9_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f72,f67,f75])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    spl9_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    sP2(k1_xboole_0) | ~spl9_2),
% 0.22/0.46    inference(superposition,[],[f71,f69])).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl9_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f67])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    ( ! [X0] : (sP2(k6_relat_1(X0))) )),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f39,f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    ( ! [X0] : (sP2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0] : (sP2(X0) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(definition_folding,[],[f13,f19,f18,f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X1,X0,X3] : (sP0(X1,X0,X3) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))),
% 0.22/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    spl9_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f38,f67])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    ~spl9_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f36,f62])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    k1_xboole_0 != sK3),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (1936)------------------------------
% 0.22/0.46  % (1936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (1936)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (1936)Memory used [KB]: 11001
% 0.22/0.46  % (1936)Time elapsed: 0.042 s
% 0.22/0.46  % (1936)------------------------------
% 0.22/0.46  % (1936)------------------------------
% 0.22/0.46  % (1916)Success in time 0.102 s
%------------------------------------------------------------------------------
