%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 211 expanded)
%              Number of leaves         :   25 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :  351 ( 674 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f110,f111,f119,f124,f170,f173,f178,f185,f188,f194,f213,f216,f240,f245,f253])).

fof(f253,plain,
    ( ~ spl4_2
    | ~ spl4_9
    | spl4_16
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_9
    | spl4_16
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f118,f80,f168,f184,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f184,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_18
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f168,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_16
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f80,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f118,plain,
    ( v1_ordinal1(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_9
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f245,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl4_23 ),
    inference(unit_resulting_resolution,[],[f68,f239])).

fof(f239,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl4_23
  <=> r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f68,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f58,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f52,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f240,plain,
    ( ~ spl4_23
    | spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f219,f163,f103,f237])).

fof(f103,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f163,plain,
    ( spl4_15
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f219,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl4_7
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f105,f165])).

fof(f165,plain,
    ( sK0 = sK1
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f105,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f216,plain,
    ( ~ spl4_1
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl4_1
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f75,f212,f152])).

fof(f152,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f42,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(condensation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f212,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_20
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f75,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f213,plain,
    ( ~ spl4_20
    | ~ spl4_15
    | spl4_17 ),
    inference(avatar_split_clause,[],[f202,f175,f163,f210])).

fof(f175,plain,
    ( spl4_17
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f202,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_15
    | spl4_17 ),
    inference(forward_demodulation,[],[f176,f165])).

fof(f176,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f194,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f75,f80,f109,f177,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f177,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f109,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_8
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f188,plain,
    ( ~ spl4_10
    | ~ spl4_16
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl4_10
    | ~ spl4_16
    | spl4_17 ),
    inference(unit_resulting_resolution,[],[f123,f169,f176,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK2(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f169,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f123,plain,
    ( v1_ordinal1(sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_10
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f185,plain,
    ( spl4_18
    | spl4_15
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f180,f175,f163,f182])).

fof(f180,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl4_17 ),
    inference(resolution,[],[f177,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f178,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_17
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f171,f107,f175,f78,f73])).

fof(f171,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f108,f42])).

fof(f108,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f173,plain,
    ( ~ spl4_16
    | spl4_7 ),
    inference(avatar_split_clause,[],[f172,f103,f167])).

fof(f172,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_7 ),
    inference(resolution,[],[f105,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f170,plain,
    ( spl4_15
    | spl4_16
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f158,f103,f167,f163])).

fof(f158,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ spl4_7 ),
    inference(resolution,[],[f67,f104])).

fof(f104,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f103])).

% (25892)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (25886)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (25888)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f124,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f113,f78,f121])).

fof(f113,plain,
    ( v1_ordinal1(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f80])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f119,plain,
    ( spl4_9
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f112,f73,f116])).

fof(f112,plain,
    ( v1_ordinal1(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f53,f75])).

fof(f111,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f64,f107,f103])).

fof(f64,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f40,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f110,plain,
    ( ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f63,f107,f103])).

fof(f63,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f41,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (25907)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.49  % (25899)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.50  % (25889)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (25891)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.50  % (25887)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.50  % (25907)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f254,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f76,f81,f110,f111,f119,f124,f170,f173,f178,f185,f188,f194,f213,f216,f240,f245,f253])).
% 0.19/0.50  fof(f253,plain,(
% 0.19/0.50    ~spl4_2 | ~spl4_9 | spl4_16 | ~spl4_18),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f250])).
% 0.19/0.50  fof(f250,plain,(
% 0.19/0.50    $false | (~spl4_2 | ~spl4_9 | spl4_16 | ~spl4_18)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f118,f80,f168,f184,f51])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.19/0.50    inference(flattening,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.19/0.50  fof(f184,plain,(
% 0.19/0.50    r2_xboole_0(sK0,sK1) | ~spl4_18),
% 0.19/0.50    inference(avatar_component_clause,[],[f182])).
% 0.19/0.50  fof(f182,plain,(
% 0.19/0.50    spl4_18 <=> r2_xboole_0(sK0,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.19/0.50  fof(f168,plain,(
% 0.19/0.50    ~r2_hidden(sK0,sK1) | spl4_16),
% 0.19/0.50    inference(avatar_component_clause,[],[f167])).
% 0.19/0.50  fof(f167,plain,(
% 0.19/0.50    spl4_16 <=> r2_hidden(sK0,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.19/0.50  fof(f80,plain,(
% 0.19/0.50    v3_ordinal1(sK1) | ~spl4_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f78])).
% 0.19/0.50  fof(f78,plain,(
% 0.19/0.50    spl4_2 <=> v3_ordinal1(sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.50  fof(f118,plain,(
% 0.19/0.50    v1_ordinal1(sK0) | ~spl4_9),
% 0.19/0.50    inference(avatar_component_clause,[],[f116])).
% 0.19/0.50  fof(f116,plain,(
% 0.19/0.50    spl4_9 <=> v1_ordinal1(sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.50  fof(f245,plain,(
% 0.19/0.50    spl4_23),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f241])).
% 0.19/0.50  fof(f241,plain,(
% 0.19/0.50    $false | spl4_23),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f68,f239])).
% 0.19/0.50  fof(f239,plain,(
% 0.19/0.50    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) | spl4_23),
% 0.19/0.50    inference(avatar_component_clause,[],[f237])).
% 0.19/0.50  fof(f237,plain,(
% 0.19/0.50    spl4_23 <=> r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.19/0.50    inference(definition_unfolding,[],[f52,f58])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.19/0.50  fof(f240,plain,(
% 0.19/0.50    ~spl4_23 | spl4_7 | ~spl4_15),
% 0.19/0.50    inference(avatar_split_clause,[],[f219,f163,f103,f237])).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    spl4_7 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.50  fof(f163,plain,(
% 0.19/0.50    spl4_15 <=> sK0 = sK1),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.50  fof(f219,plain,(
% 0.19/0.50    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) | (spl4_7 | ~spl4_15)),
% 0.19/0.50    inference(forward_demodulation,[],[f105,f165])).
% 0.19/0.50  fof(f165,plain,(
% 0.19/0.50    sK0 = sK1 | ~spl4_15),
% 0.19/0.50    inference(avatar_component_clause,[],[f163])).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | spl4_7),
% 0.19/0.50    inference(avatar_component_clause,[],[f103])).
% 0.19/0.50  fof(f216,plain,(
% 0.19/0.50    ~spl4_1 | spl4_20),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f214])).
% 0.19/0.50  fof(f214,plain,(
% 0.19/0.50    $false | (~spl4_1 | spl4_20)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f75,f212,f152])).
% 0.19/0.50  fof(f152,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tarski(X0,X0) | ~v3_ordinal1(X0)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f151])).
% 0.19/0.50  fof(f151,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tarski(X0,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.19/0.50    inference(resolution,[],[f42,f71])).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0)) )),
% 0.19/0.50    inference(condensation,[],[f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.19/0.50    inference(flattening,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_ordinal1(X0,X0) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => r1_ordinal1(X0,X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.19/0.50    inference(nnf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.19/0.50    inference(flattening,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.19/0.50  fof(f212,plain,(
% 0.19/0.50    ~r1_tarski(sK0,sK0) | spl4_20),
% 0.19/0.50    inference(avatar_component_clause,[],[f210])).
% 0.19/0.50  fof(f210,plain,(
% 0.19/0.50    spl4_20 <=> r1_tarski(sK0,sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    v3_ordinal1(sK0) | ~spl4_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f73])).
% 0.19/0.50  fof(f73,plain,(
% 0.19/0.50    spl4_1 <=> v3_ordinal1(sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.50  fof(f213,plain,(
% 0.19/0.50    ~spl4_20 | ~spl4_15 | spl4_17),
% 0.19/0.50    inference(avatar_split_clause,[],[f202,f175,f163,f210])).
% 0.19/0.50  fof(f175,plain,(
% 0.19/0.50    spl4_17 <=> r1_tarski(sK0,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.19/0.50  fof(f202,plain,(
% 0.19/0.50    ~r1_tarski(sK0,sK0) | (~spl4_15 | spl4_17)),
% 0.19/0.50    inference(forward_demodulation,[],[f176,f165])).
% 0.19/0.50  fof(f176,plain,(
% 0.19/0.50    ~r1_tarski(sK0,sK1) | spl4_17),
% 0.19/0.50    inference(avatar_component_clause,[],[f175])).
% 0.19/0.50  fof(f194,plain,(
% 0.19/0.50    ~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_17),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f191])).
% 0.19/0.50  fof(f191,plain,(
% 0.19/0.50    $false | (~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_17)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f75,f80,f109,f177,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f27])).
% 0.19/0.50  fof(f177,plain,(
% 0.19/0.50    r1_tarski(sK0,sK1) | ~spl4_17),
% 0.19/0.50    inference(avatar_component_clause,[],[f175])).
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    ~r1_ordinal1(sK0,sK1) | spl4_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f107])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    spl4_8 <=> r1_ordinal1(sK0,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.50  fof(f188,plain,(
% 0.19/0.50    ~spl4_10 | ~spl4_16 | spl4_17),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f187])).
% 0.19/0.50  fof(f187,plain,(
% 0.19/0.50    $false | (~spl4_10 | ~spl4_16 | spl4_17)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f123,f169,f176,f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | r1_tarski(X2,X0) | ~v1_ordinal1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.19/0.50    inference(rectify,[],[f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.19/0.50    inference(nnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.19/0.50  fof(f169,plain,(
% 0.19/0.50    r2_hidden(sK0,sK1) | ~spl4_16),
% 0.19/0.50    inference(avatar_component_clause,[],[f167])).
% 0.19/0.50  fof(f123,plain,(
% 0.19/0.50    v1_ordinal1(sK1) | ~spl4_10),
% 0.19/0.50    inference(avatar_component_clause,[],[f121])).
% 0.19/0.50  fof(f121,plain,(
% 0.19/0.50    spl4_10 <=> v1_ordinal1(sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.50  fof(f185,plain,(
% 0.19/0.50    spl4_18 | spl4_15 | ~spl4_17),
% 0.19/0.50    inference(avatar_split_clause,[],[f180,f175,f163,f182])).
% 0.19/0.50  fof(f180,plain,(
% 0.19/0.50    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl4_17),
% 0.19/0.50    inference(resolution,[],[f177,f57])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.19/0.50    inference(flattening,[],[f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.19/0.50    inference(nnf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.19/0.50  fof(f178,plain,(
% 0.19/0.50    ~spl4_1 | ~spl4_2 | spl4_17 | ~spl4_8),
% 0.19/0.50    inference(avatar_split_clause,[],[f171,f107,f175,f78,f73])).
% 0.19/0.50  fof(f171,plain,(
% 0.19/0.50    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl4_8),
% 0.19/0.50    inference(resolution,[],[f108,f42])).
% 0.19/0.50  fof(f108,plain,(
% 0.19/0.50    r1_ordinal1(sK0,sK1) | ~spl4_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f107])).
% 0.19/0.50  fof(f173,plain,(
% 0.19/0.50    ~spl4_16 | spl4_7),
% 0.19/0.50    inference(avatar_split_clause,[],[f172,f103,f167])).
% 0.19/0.50  fof(f172,plain,(
% 0.19/0.50    ~r2_hidden(sK0,sK1) | spl4_7),
% 0.19/0.50    inference(resolution,[],[f105,f66])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 0.19/0.50    inference(definition_unfolding,[],[f46,f58])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.19/0.50    inference(flattening,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.19/0.50    inference(nnf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.19/0.50  fof(f170,plain,(
% 0.19/0.50    spl4_15 | spl4_16 | ~spl4_7),
% 0.19/0.50    inference(avatar_split_clause,[],[f158,f103,f167,f163])).
% 0.19/0.50  fof(f158,plain,(
% 0.19/0.50    r2_hidden(sK0,sK1) | sK0 = sK1 | ~spl4_7),
% 0.19/0.50    inference(resolution,[],[f67,f104])).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl4_7),
% 0.19/0.50    inference(avatar_component_clause,[],[f103])).
% 0.19/0.50  % (25892)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.50  % (25886)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.50  % (25888)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.19/0.50    inference(definition_unfolding,[],[f45,f58])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f124,plain,(
% 0.19/0.50    spl4_10 | ~spl4_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f113,f78,f121])).
% 0.19/0.50  fof(f113,plain,(
% 0.19/0.50    v1_ordinal1(sK1) | ~spl4_2),
% 0.19/0.50    inference(resolution,[],[f53,f80])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.19/0.50  fof(f119,plain,(
% 0.19/0.50    spl4_9 | ~spl4_1),
% 0.19/0.50    inference(avatar_split_clause,[],[f112,f73,f116])).
% 0.19/0.50  fof(f112,plain,(
% 0.19/0.50    v1_ordinal1(sK0) | ~spl4_1),
% 0.19/0.50    inference(resolution,[],[f53,f75])).
% 0.19/0.50  fof(f111,plain,(
% 0.19/0.50    spl4_7 | spl4_8),
% 0.19/0.50    inference(avatar_split_clause,[],[f64,f107,f103])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.19/0.50    inference(definition_unfolding,[],[f40,f58])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.19/0.50    inference(flattening,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.19/0.50    inference(nnf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,negated_conjecture,(
% 0.19/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.19/0.50    inference(negated_conjecture,[],[f11])).
% 0.19/0.50  fof(f11,conjecture,(
% 0.19/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.19/0.50  fof(f110,plain,(
% 0.19/0.50    ~spl4_7 | ~spl4_8),
% 0.19/0.50    inference(avatar_split_clause,[],[f63,f107,f103])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.19/0.50    inference(definition_unfolding,[],[f41,f58])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f26])).
% 0.19/0.50  fof(f81,plain,(
% 0.19/0.50    spl4_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f39,f78])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    v3_ordinal1(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f26])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    spl4_1),
% 0.19/0.50    inference(avatar_split_clause,[],[f38,f73])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    v3_ordinal1(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f26])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (25907)------------------------------
% 0.19/0.50  % (25907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (25907)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (25907)Memory used [KB]: 10874
% 0.19/0.50  % (25907)Time elapsed: 0.083 s
% 0.19/0.50  % (25907)------------------------------
% 0.19/0.50  % (25907)------------------------------
% 0.19/0.51  % (25880)Success in time 0.154 s
%------------------------------------------------------------------------------
