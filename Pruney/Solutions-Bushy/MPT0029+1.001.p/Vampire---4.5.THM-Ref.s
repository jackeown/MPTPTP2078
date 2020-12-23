%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0029+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 106 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  238 ( 405 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f71,f267,f298,f299,f329])).

fof(f329,plain,
    ( ~ spl8_7
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f323,f297])).

fof(f297,plain,
    ( ~ r2_hidden(sK7(sK4,k3_xboole_0(sK4,sK5),sK4),sK4)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl8_8
  <=> r2_hidden(sK7(sK4,k3_xboole_0(sK4,sK5),sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f323,plain,
    ( r2_hidden(sK7(sK4,k3_xboole_0(sK4,sK5),sK4),sK4)
    | ~ spl8_7 ),
    inference(resolution,[],[f291,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f291,plain,
    ( sP0(sK5,sK7(sK4,k3_xboole_0(sK4,sK5),sK4),sK4)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl8_7
  <=> sP0(sK5,sK7(sK4,k3_xboole_0(sK4,sK5),sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f299,plain,
    ( spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f278,f264,f289])).

fof(f264,plain,
    ( spl8_5
  <=> r2_hidden(sK7(sK4,k3_xboole_0(sK4,sK5),sK4),k3_xboole_0(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f278,plain,
    ( sP0(sK5,sK7(sK4,k3_xboole_0(sK4,sK5),sK4),sK4)
    | ~ spl8_5 ),
    inference(resolution,[],[f266,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f31,f49])).

fof(f49,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f7,f6])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f266,plain,
    ( r2_hidden(sK7(sK4,k3_xboole_0(sK4,sK5),sK4),k3_xboole_0(sK4,sK5))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f264])).

fof(f298,plain,
    ( ~ spl8_8
    | spl8_2
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f269,f264,f68,f295])).

fof(f68,plain,
    ( spl8_2
  <=> sP3(sK4,k3_xboole_0(sK4,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f269,plain,
    ( ~ r2_hidden(sK7(sK4,k3_xboole_0(sK4,sK5),sK4),sK4)
    | spl8_2
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f70,f266,f116])).

fof(f116,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK7(X3,X4,X5),X5)
      | sP3(X3,X4,X5)
      | ~ r2_hidden(sK7(X3,X4,X5),X4) ) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X1,sK7(X0,X1,X2),X0)
      | sP3(X0,X1,X2)
      | ~ r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP2(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP2(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f70,plain,
    ( ~ sP3(sK4,k3_xboole_0(sK4,sK5),sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f267,plain,
    ( spl8_5
    | spl8_2 ),
    inference(avatar_split_clause,[],[f256,f68,f264])).

fof(f256,plain,
    ( r2_hidden(sK7(sK4,k3_xboole_0(sK4,sK5),sK4),k3_xboole_0(sK4,sK5))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f70,f219])).

fof(f219,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,X0),X1)
      | sP3(X0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f215,f117])).

fof(f117,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK7(X6,X7,X8),X8)
      | sP3(X6,X7,X8)
      | ~ r2_hidden(sK7(X6,X7,X8),X6) ) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f215,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,X0),X0)
      | sP3(X0,X1,X0)
      | r2_hidden(sK7(X0,X1,X0),X1) ) ),
    inference(factoring,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | sP3(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,sK7(X0,X1,X2),X0)
      | sP3(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,
    ( ~ spl8_2
    | spl8_1 ),
    inference(avatar_split_clause,[],[f62,f52,f68])).

fof(f52,plain,
    ( spl8_1
  <=> sK4 = k2_xboole_0(sK4,k3_xboole_0(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f62,plain,
    ( ~ sP3(sK4,k3_xboole_0(sK4,sK5),sK4)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f54,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f10,f9])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f54,plain,
    ( sK4 != k2_xboole_0(sK4,k3_xboole_0(sK4,sK5))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f55,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f30,plain,(
    sK4 != k2_xboole_0(sK4,k3_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    sK4 != k2_xboole_0(sK4,k3_xboole_0(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f5,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
   => sK4 != k2_xboole_0(sK4,k3_xboole_0(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

%------------------------------------------------------------------------------
