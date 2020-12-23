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
% DateTime   : Thu Dec  3 12:43:15 EST 2020

% Result     : Theorem 2.61s
% Output     : Refutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 256 expanded)
%              Number of leaves         :   26 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  287 ( 569 expanded)
%              Number of equality atoms :   76 ( 189 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f113,f118,f150,f158,f163,f178,f1771,f1882,f1890,f1896,f1943,f1954,f2100,f2123])).

fof(f2123,plain,
    ( ~ spl8_1
    | ~ spl8_6
    | spl8_34
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(avatar_contradiction_clause,[],[f2107])).

fof(f2107,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_6
    | spl8_34
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(unit_resulting_resolution,[],[f77,f92,f76,f1942,f1765,f2099,f217])).

fof(f217,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,X3)
        | ~ r1_tarski(X1,sK2)
        | sK3 = X0
        | ~ r1_tarski(X2,sK1)
        | ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X3,X2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f205,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,sK2)
        | sK3 = X0
        | ~ r1_tarski(X2,sK1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f193,f35])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | sK3 = X0
        | ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,sK2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f191,f35])).

fof(f191,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ r2_hidden(X2,sK1)
        | sK3 = X2 )
    | ~ spl8_6 ),
    inference(resolution,[],[f164,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f164,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k4_xboole_0(sK1,sK2))
        | sK3 = X0
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f132,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
        | sK3 = X0 )
    | ~ spl8_6 ),
    inference(superposition,[],[f78,f117])).

fof(f117,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_6
  <=> k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f2099,plain,
    ( r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK2)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f2097])).

fof(f2097,plain,
    ( spl8_44
  <=> r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f1765,plain,
    ( sK3 != sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl8_34 ),
    inference(avatar_component_clause,[],[f1764])).

fof(f1764,plain,
    ( spl8_34
  <=> sK3 = sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f1942,plain,
    ( r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK0)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f1940])).

fof(f1940,plain,
    ( spl8_40
  <=> r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f92,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2100,plain,
    ( ~ spl8_40
    | spl8_44
    | spl8_41 ),
    inference(avatar_split_clause,[],[f1955,f1951,f2097,f1940])).

fof(f1951,plain,
    ( spl8_41
  <=> r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f1955,plain,
    ( r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK0)
    | spl8_41 ),
    inference(resolution,[],[f1953,f81])).

fof(f1953,plain,
    ( ~ r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2))
    | spl8_41 ),
    inference(avatar_component_clause,[],[f1951])).

fof(f1954,plain,
    ( ~ spl8_41
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f1935,f1768,f1951])).

fof(f1768,plain,
    ( spl8_35
  <=> r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1935,plain,
    ( ~ r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl8_35 ),
    inference(resolution,[],[f1770,f82])).

fof(f1770,plain,
    ( r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f1943,plain,
    ( spl8_40
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f1934,f1768,f1940])).

fof(f1934,plain,
    ( r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK0)
    | ~ spl8_35 ),
    inference(resolution,[],[f1770,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1896,plain,
    ( ~ spl8_10
    | ~ spl8_39 ),
    inference(avatar_contradiction_clause,[],[f1891])).

fof(f1891,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_39 ),
    inference(unit_resulting_resolution,[],[f177,f1889,f82])).

fof(f1889,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK0,sK2))
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f1887])).

fof(f1887,plain,
    ( spl8_39
  <=> r2_hidden(sK3,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f177,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl8_10
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f1890,plain,
    ( ~ spl8_2
    | spl8_39
    | spl8_38 ),
    inference(avatar_split_clause,[],[f1883,f1879,f1887,f95])).

fof(f95,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1879,plain,
    ( spl8_38
  <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f1883,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK0,sK2))
    | ~ r2_hidden(sK3,sK0)
    | spl8_38 ),
    inference(resolution,[],[f1881,f81])).

fof(f1881,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl8_38 ),
    inference(avatar_component_clause,[],[f1879])).

fof(f1882,plain,
    ( ~ spl8_38
    | spl8_5
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f1877,f1764,f110,f1879])).

fof(f110,plain,
    ( spl8_5
  <=> k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1877,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl8_5
    | ~ spl8_34 ),
    inference(trivial_inequality_removal,[],[f1876])).

fof(f1876,plain,
    ( sK3 != sK3
    | ~ r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl8_5
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f1875,f1766])).

fof(f1766,plain,
    ( sK3 = sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f1764])).

fof(f1875,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | sK3 != sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl8_5
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f268,f1766])).

fof(f268,plain,
    ( ~ r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | sK3 != sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl8_5 ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,
    ( ! [X1] :
        ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X1
        | ~ r2_hidden(sK5(sK3,X1),X1)
        | sK3 != sK5(sK3,X1) )
    | spl8_5 ),
    inference(superposition,[],[f112,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) != X0 ) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f112,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1771,plain,
    ( spl8_34
    | spl8_35
    | spl8_5 ),
    inference(avatar_split_clause,[],[f216,f110,f1768,f1764])).

fof(f216,plain,
    ( r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | sK3 = sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl8_5 ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,
    ( ! [X0] :
        ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
        | r2_hidden(sK5(sK3,X0),X0)
        | sK3 = sK5(sK3,X0) )
    | spl8_5 ),
    inference(superposition,[],[f112,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f178,plain,
    ( ~ spl8_8
    | spl8_10
    | spl8_9 ),
    inference(avatar_split_clause,[],[f172,f160,f175,f155])).

fof(f155,plain,
    ( spl8_8
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f160,plain,
    ( spl8_9
  <=> r2_hidden(sK3,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f172,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK3,sK1)
    | spl8_9 ),
    inference(resolution,[],[f162,f81])).

fof(f162,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK1,sK2))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f163,plain,
    ( ~ spl8_9
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f152,f145,f160])).

fof(f145,plain,
    ( spl8_7
  <=> r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f152,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK1,sK2))
    | ~ spl8_7 ),
    inference(resolution,[],[f147,f82])).

fof(f147,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f145])).

fof(f158,plain,
    ( spl8_8
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f151,f145,f155])).

fof(f151,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl8_7 ),
    inference(resolution,[],[f147,f83])).

fof(f150,plain,
    ( spl8_7
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f140,f115,f145])).

fof(f140,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl8_6 ),
    inference(superposition,[],[f85,f117])).

fof(f85,plain,(
    ! [X0,X3] : r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f118,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f61,f115])).

fof(f61,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f23,f30,f59])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f113,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f60,f110])).

fof(f60,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f25,f59,f30])).

fof(f25,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f24,f95])).

fof(f24,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f22,f90])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (24009)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (24016)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24024)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (24017)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (24006)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (24015)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (24005)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (24023)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (24004)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (24011)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (24008)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (24030)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (24026)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (24032)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (24021)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (24022)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (24019)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (24027)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (24012)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (24020)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (24014)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (24013)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (24029)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (24007)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (24028)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (24021)Refutation not found, incomplete strategy% (24021)------------------------------
% 0.21/0.57  % (24021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (24021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24021)Memory used [KB]: 10746
% 0.21/0.57  % (24021)Time elapsed: 0.148 s
% 0.21/0.57  % (24021)------------------------------
% 0.21/0.57  % (24021)------------------------------
% 1.70/0.58  % (24025)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.70/0.59  % (24018)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.70/0.59  % (24033)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.70/0.59  % (24010)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.70/0.59  % (24031)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.61/0.71  % (24034)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.61/0.76  % (24026)Refutation found. Thanks to Tanya!
% 2.61/0.76  % SZS status Theorem for theBenchmark
% 2.61/0.76  % SZS output start Proof for theBenchmark
% 2.61/0.76  fof(f2124,plain,(
% 2.61/0.76    $false),
% 2.61/0.76    inference(avatar_sat_refutation,[],[f93,f98,f113,f118,f150,f158,f163,f178,f1771,f1882,f1890,f1896,f1943,f1954,f2100,f2123])).
% 2.61/0.76  fof(f2123,plain,(
% 2.61/0.76    ~spl8_1 | ~spl8_6 | spl8_34 | ~spl8_40 | ~spl8_44),
% 2.61/0.76    inference(avatar_contradiction_clause,[],[f2107])).
% 2.61/0.76  fof(f2107,plain,(
% 2.61/0.76    $false | (~spl8_1 | ~spl8_6 | spl8_34 | ~spl8_40 | ~spl8_44)),
% 2.61/0.76    inference(unit_resulting_resolution,[],[f77,f92,f76,f1942,f1765,f2099,f217])).
% 2.61/0.76  fof(f217,plain,(
% 2.61/0.76    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X3) | ~r1_tarski(X1,sK2) | sK3 = X0 | ~r1_tarski(X2,sK1) | ~r2_hidden(X0,X1) | ~r1_tarski(X3,X2)) ) | ~spl8_6),
% 2.61/0.76    inference(resolution,[],[f205,f35])).
% 2.61/0.76  fof(f35,plain,(
% 2.61/0.76    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.61/0.76    inference(cnf_transformation,[],[f21])).
% 2.61/0.76  fof(f21,plain,(
% 2.61/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.61/0.76    inference(ennf_transformation,[],[f2])).
% 2.61/0.76  fof(f2,axiom,(
% 2.61/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.61/0.76  fof(f205,plain,(
% 2.61/0.76    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r1_tarski(X1,sK2) | sK3 = X0 | ~r1_tarski(X2,sK1)) ) | ~spl8_6),
% 2.61/0.76    inference(resolution,[],[f193,f35])).
% 2.61/0.76  fof(f193,plain,(
% 2.61/0.76    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | sK3 = X0 | ~r2_hidden(X0,X1) | ~r1_tarski(X1,sK2)) ) | ~spl8_6),
% 2.61/0.76    inference(resolution,[],[f191,f35])).
% 2.61/0.76  fof(f191,plain,(
% 2.61/0.76    ( ! [X2] : (~r2_hidden(X2,sK2) | ~r2_hidden(X2,sK1) | sK3 = X2) ) | ~spl8_6),
% 2.61/0.76    inference(resolution,[],[f164,f82])).
% 2.61/0.76  fof(f82,plain,(
% 2.61/0.76    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 2.61/0.76    inference(equality_resolution,[],[f48])).
% 2.61/0.76  fof(f48,plain,(
% 2.61/0.76    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.61/0.76    inference(cnf_transformation,[],[f3])).
% 2.61/0.76  fof(f3,axiom,(
% 2.61/0.76    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.61/0.76  fof(f164,plain,(
% 2.61/0.76    ( ! [X0] : (r2_hidden(X0,k4_xboole_0(sK1,sK2)) | sK3 = X0 | ~r2_hidden(X0,sK1)) ) | ~spl8_6),
% 2.61/0.76    inference(resolution,[],[f132,f81])).
% 2.61/0.76  fof(f81,plain,(
% 2.61/0.76    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 2.61/0.76    inference(equality_resolution,[],[f49])).
% 2.61/0.76  fof(f49,plain,(
% 2.61/0.76    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.61/0.76    inference(cnf_transformation,[],[f3])).
% 2.61/0.76  fof(f132,plain,(
% 2.61/0.76    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | sK3 = X0) ) | ~spl8_6),
% 2.61/0.76    inference(superposition,[],[f78,f117])).
% 2.61/0.76  fof(f117,plain,(
% 2.61/0.76    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl8_6),
% 2.61/0.76    inference(avatar_component_clause,[],[f115])).
% 2.61/0.76  fof(f115,plain,(
% 2.61/0.76    spl8_6 <=> k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.61/0.76  fof(f78,plain,(
% 2.61/0.76    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 2.61/0.76    inference(equality_resolution,[],[f67])).
% 2.61/0.76  fof(f67,plain,(
% 2.61/0.76    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.61/0.76    inference(definition_unfolding,[],[f39,f59])).
% 2.61/0.76  fof(f59,plain,(
% 2.61/0.76    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.61/0.76    inference(definition_unfolding,[],[f26,f58])).
% 2.61/0.76  fof(f58,plain,(
% 2.61/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.61/0.76    inference(definition_unfolding,[],[f29,f57])).
% 2.61/0.76  fof(f57,plain,(
% 2.61/0.76    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.61/0.76    inference(definition_unfolding,[],[f42,f56])).
% 2.61/0.76  fof(f56,plain,(
% 2.61/0.76    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.61/0.76    inference(cnf_transformation,[],[f14])).
% 2.61/0.76  fof(f14,axiom,(
% 2.61/0.76    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.61/0.76  fof(f42,plain,(
% 2.61/0.76    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.61/0.76    inference(cnf_transformation,[],[f13])).
% 2.61/0.76  fof(f13,axiom,(
% 2.61/0.76    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.61/0.76  fof(f29,plain,(
% 2.61/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.61/0.76    inference(cnf_transformation,[],[f12])).
% 2.61/0.76  fof(f12,axiom,(
% 2.61/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.61/0.76  fof(f26,plain,(
% 2.61/0.76    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.61/0.76    inference(cnf_transformation,[],[f11])).
% 2.61/0.76  fof(f11,axiom,(
% 2.61/0.76    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.61/0.76  fof(f39,plain,(
% 2.61/0.76    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.61/0.76    inference(cnf_transformation,[],[f9])).
% 2.61/0.76  fof(f9,axiom,(
% 2.61/0.76    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.61/0.76  fof(f2099,plain,(
% 2.61/0.76    r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK2) | ~spl8_44),
% 2.61/0.76    inference(avatar_component_clause,[],[f2097])).
% 2.61/0.76  fof(f2097,plain,(
% 2.61/0.76    spl8_44 <=> r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK2)),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 2.61/0.76  fof(f1765,plain,(
% 2.61/0.76    sK3 != sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl8_34),
% 2.61/0.76    inference(avatar_component_clause,[],[f1764])).
% 2.61/0.76  fof(f1764,plain,(
% 2.61/0.76    spl8_34 <=> sK3 = sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 2.61/0.76  fof(f1942,plain,(
% 2.61/0.76    r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK0) | ~spl8_40),
% 2.61/0.76    inference(avatar_component_clause,[],[f1940])).
% 2.61/0.76  fof(f1940,plain,(
% 2.61/0.76    spl8_40 <=> r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK0)),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 2.61/0.76  fof(f76,plain,(
% 2.61/0.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.61/0.76    inference(equality_resolution,[],[f33])).
% 2.61/0.76  fof(f33,plain,(
% 2.61/0.76    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.61/0.76    inference(cnf_transformation,[],[f5])).
% 2.61/0.76  fof(f5,axiom,(
% 2.61/0.76    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.61/0.76  fof(f92,plain,(
% 2.61/0.76    r1_tarski(sK0,sK1) | ~spl8_1),
% 2.61/0.76    inference(avatar_component_clause,[],[f90])).
% 2.61/0.76  fof(f90,plain,(
% 2.61/0.76    spl8_1 <=> r1_tarski(sK0,sK1)),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.61/0.76  fof(f77,plain,(
% 2.61/0.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.61/0.76    inference(equality_resolution,[],[f32])).
% 2.61/0.76  fof(f32,plain,(
% 2.61/0.76    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.61/0.76    inference(cnf_transformation,[],[f5])).
% 2.61/0.76  fof(f2100,plain,(
% 2.61/0.76    ~spl8_40 | spl8_44 | spl8_41),
% 2.61/0.76    inference(avatar_split_clause,[],[f1955,f1951,f2097,f1940])).
% 2.61/0.76  fof(f1951,plain,(
% 2.61/0.76    spl8_41 <=> r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 2.61/0.76  fof(f1955,plain,(
% 2.61/0.76    r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK2) | ~r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK0) | spl8_41),
% 2.61/0.76    inference(resolution,[],[f1953,f81])).
% 2.61/0.76  fof(f1953,plain,(
% 2.61/0.76    ~r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2)) | spl8_41),
% 2.61/0.76    inference(avatar_component_clause,[],[f1951])).
% 2.61/0.76  fof(f1954,plain,(
% 2.61/0.76    ~spl8_41 | ~spl8_35),
% 2.61/0.76    inference(avatar_split_clause,[],[f1935,f1768,f1951])).
% 2.61/0.76  fof(f1768,plain,(
% 2.61/0.76    spl8_35 <=> r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 2.61/0.76  fof(f1935,plain,(
% 2.61/0.76    ~r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2)) | ~spl8_35),
% 2.61/0.76    inference(resolution,[],[f1770,f82])).
% 2.61/0.76  fof(f1770,plain,(
% 2.61/0.76    r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | ~spl8_35),
% 2.61/0.76    inference(avatar_component_clause,[],[f1768])).
% 2.61/0.76  fof(f1943,plain,(
% 2.61/0.76    spl8_40 | ~spl8_35),
% 2.61/0.76    inference(avatar_split_clause,[],[f1934,f1768,f1940])).
% 2.61/0.76  fof(f1934,plain,(
% 2.61/0.76    r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),sK0) | ~spl8_35),
% 2.61/0.76    inference(resolution,[],[f1770,f83])).
% 2.61/0.76  fof(f83,plain,(
% 2.61/0.76    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 2.61/0.76    inference(equality_resolution,[],[f47])).
% 2.61/0.76  fof(f47,plain,(
% 2.61/0.76    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.61/0.76    inference(cnf_transformation,[],[f3])).
% 2.61/0.76  fof(f1896,plain,(
% 2.61/0.76    ~spl8_10 | ~spl8_39),
% 2.61/0.76    inference(avatar_contradiction_clause,[],[f1891])).
% 2.61/0.76  fof(f1891,plain,(
% 2.61/0.76    $false | (~spl8_10 | ~spl8_39)),
% 2.61/0.76    inference(unit_resulting_resolution,[],[f177,f1889,f82])).
% 2.61/0.76  fof(f1889,plain,(
% 2.61/0.76    r2_hidden(sK3,k4_xboole_0(sK0,sK2)) | ~spl8_39),
% 2.61/0.76    inference(avatar_component_clause,[],[f1887])).
% 2.61/0.76  fof(f1887,plain,(
% 2.61/0.76    spl8_39 <=> r2_hidden(sK3,k4_xboole_0(sK0,sK2))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 2.61/0.76  fof(f177,plain,(
% 2.61/0.76    r2_hidden(sK3,sK2) | ~spl8_10),
% 2.61/0.76    inference(avatar_component_clause,[],[f175])).
% 2.61/0.76  fof(f175,plain,(
% 2.61/0.76    spl8_10 <=> r2_hidden(sK3,sK2)),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.61/0.76  fof(f1890,plain,(
% 2.61/0.76    ~spl8_2 | spl8_39 | spl8_38),
% 2.61/0.76    inference(avatar_split_clause,[],[f1883,f1879,f1887,f95])).
% 2.61/0.76  fof(f95,plain,(
% 2.61/0.76    spl8_2 <=> r2_hidden(sK3,sK0)),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.61/0.76  fof(f1879,plain,(
% 2.61/0.76    spl8_38 <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 2.61/0.76  fof(f1883,plain,(
% 2.61/0.76    r2_hidden(sK3,k4_xboole_0(sK0,sK2)) | ~r2_hidden(sK3,sK0) | spl8_38),
% 2.61/0.76    inference(resolution,[],[f1881,f81])).
% 2.61/0.76  fof(f1881,plain,(
% 2.61/0.76    ~r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl8_38),
% 2.61/0.76    inference(avatar_component_clause,[],[f1879])).
% 2.61/0.76  fof(f1882,plain,(
% 2.61/0.76    ~spl8_38 | spl8_5 | ~spl8_34),
% 2.61/0.76    inference(avatar_split_clause,[],[f1877,f1764,f110,f1879])).
% 2.61/0.76  fof(f110,plain,(
% 2.61/0.76    spl8_5 <=> k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.61/0.76  fof(f1877,plain,(
% 2.61/0.76    ~r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (spl8_5 | ~spl8_34)),
% 2.61/0.76    inference(trivial_inequality_removal,[],[f1876])).
% 2.61/0.76  fof(f1876,plain,(
% 2.61/0.76    sK3 != sK3 | ~r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (spl8_5 | ~spl8_34)),
% 2.61/0.76    inference(forward_demodulation,[],[f1875,f1766])).
% 2.61/0.76  fof(f1766,plain,(
% 2.61/0.76    sK3 = sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | ~spl8_34),
% 2.61/0.76    inference(avatar_component_clause,[],[f1764])).
% 2.61/0.76  fof(f1875,plain,(
% 2.61/0.76    ~r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | sK3 != sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (spl8_5 | ~spl8_34)),
% 2.61/0.76    inference(forward_demodulation,[],[f268,f1766])).
% 2.61/0.76  fof(f268,plain,(
% 2.61/0.76    ~r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | sK3 != sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl8_5),
% 2.61/0.76    inference(equality_resolution,[],[f120])).
% 2.61/0.76  fof(f120,plain,(
% 2.61/0.76    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X1 | ~r2_hidden(sK5(sK3,X1),X1) | sK3 != sK5(sK3,X1)) ) | spl8_5),
% 2.61/0.76    inference(superposition,[],[f112,f65])).
% 2.61/0.76  fof(f65,plain,(
% 2.61/0.76    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | ~r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) != X0) )),
% 2.61/0.76    inference(definition_unfolding,[],[f41,f59])).
% 2.61/0.76  fof(f41,plain,(
% 2.61/0.76    ( ! [X0,X1] : (sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 2.61/0.76    inference(cnf_transformation,[],[f9])).
% 2.61/0.76  fof(f112,plain,(
% 2.61/0.76    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl8_5),
% 2.61/0.76    inference(avatar_component_clause,[],[f110])).
% 2.61/0.76  fof(f1771,plain,(
% 2.61/0.76    spl8_34 | spl8_35 | spl8_5),
% 2.61/0.76    inference(avatar_split_clause,[],[f216,f110,f1768,f1764])).
% 2.61/0.76  fof(f216,plain,(
% 2.61/0.76    r2_hidden(sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | sK3 = sK5(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl8_5),
% 2.61/0.76    inference(equality_resolution,[],[f119])).
% 2.61/0.76  fof(f119,plain,(
% 2.61/0.76    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0 | r2_hidden(sK5(sK3,X0),X0) | sK3 = sK5(sK3,X0)) ) | spl8_5),
% 2.61/0.76    inference(superposition,[],[f112,f66])).
% 2.61/0.76  fof(f66,plain,(
% 2.61/0.76    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) = X0) )),
% 2.61/0.76    inference(definition_unfolding,[],[f40,f59])).
% 2.61/0.76  fof(f40,plain,(
% 2.61/0.76    ( ! [X0,X1] : (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 2.61/0.76    inference(cnf_transformation,[],[f9])).
% 2.61/0.76  fof(f178,plain,(
% 2.61/0.76    ~spl8_8 | spl8_10 | spl8_9),
% 2.61/0.76    inference(avatar_split_clause,[],[f172,f160,f175,f155])).
% 2.61/0.76  fof(f155,plain,(
% 2.61/0.76    spl8_8 <=> r2_hidden(sK3,sK1)),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.61/0.76  fof(f160,plain,(
% 2.61/0.76    spl8_9 <=> r2_hidden(sK3,k4_xboole_0(sK1,sK2))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.61/0.76  fof(f172,plain,(
% 2.61/0.76    r2_hidden(sK3,sK2) | ~r2_hidden(sK3,sK1) | spl8_9),
% 2.61/0.76    inference(resolution,[],[f162,f81])).
% 2.61/0.76  fof(f162,plain,(
% 2.61/0.76    ~r2_hidden(sK3,k4_xboole_0(sK1,sK2)) | spl8_9),
% 2.61/0.76    inference(avatar_component_clause,[],[f160])).
% 2.61/0.76  fof(f163,plain,(
% 2.61/0.76    ~spl8_9 | ~spl8_7),
% 2.61/0.76    inference(avatar_split_clause,[],[f152,f145,f160])).
% 2.61/0.76  fof(f145,plain,(
% 2.61/0.76    spl8_7 <=> r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 2.61/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.61/0.76  fof(f152,plain,(
% 2.61/0.76    ~r2_hidden(sK3,k4_xboole_0(sK1,sK2)) | ~spl8_7),
% 2.61/0.76    inference(resolution,[],[f147,f82])).
% 2.61/0.76  fof(f147,plain,(
% 2.61/0.76    r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl8_7),
% 2.61/0.76    inference(avatar_component_clause,[],[f145])).
% 2.61/0.76  fof(f158,plain,(
% 2.61/0.76    spl8_8 | ~spl8_7),
% 2.61/0.76    inference(avatar_split_clause,[],[f151,f145,f155])).
% 2.61/0.76  fof(f151,plain,(
% 2.61/0.76    r2_hidden(sK3,sK1) | ~spl8_7),
% 2.61/0.76    inference(resolution,[],[f147,f83])).
% 2.61/0.76  fof(f150,plain,(
% 2.61/0.76    spl8_7 | ~spl8_6),
% 2.61/0.76    inference(avatar_split_clause,[],[f140,f115,f145])).
% 2.61/0.76  fof(f140,plain,(
% 2.61/0.76    r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl8_6),
% 2.61/0.76    inference(superposition,[],[f85,f117])).
% 2.61/0.76  fof(f85,plain,(
% 2.61/0.76    ( ! [X0,X3] : (r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X3))) )),
% 2.61/0.76    inference(equality_resolution,[],[f84])).
% 2.61/0.76  fof(f84,plain,(
% 2.61/0.76    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X3) != X2) )),
% 2.61/0.76    inference(equality_resolution,[],[f70])).
% 2.61/0.76  fof(f70,plain,(
% 2.61/0.76    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 2.61/0.76    inference(definition_unfolding,[],[f55,f58])).
% 2.61/0.76  fof(f55,plain,(
% 2.61/0.76    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.61/0.76    inference(cnf_transformation,[],[f10])).
% 2.61/0.76  fof(f10,axiom,(
% 2.61/0.76    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.61/0.76  fof(f118,plain,(
% 2.61/0.76    spl8_6),
% 2.61/0.76    inference(avatar_split_clause,[],[f61,f115])).
% 2.61/0.76  fof(f61,plain,(
% 2.61/0.76    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.61/0.76    inference(definition_unfolding,[],[f23,f30,f59])).
% 2.61/0.76  fof(f30,plain,(
% 2.61/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.61/0.76    inference(cnf_transformation,[],[f8])).
% 2.61/0.76  fof(f8,axiom,(
% 2.61/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.61/0.76  fof(f23,plain,(
% 2.61/0.76    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 2.61/0.76    inference(cnf_transformation,[],[f19])).
% 2.61/0.76  fof(f19,plain,(
% 2.61/0.76    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 2.61/0.76    inference(flattening,[],[f18])).
% 2.61/0.76  fof(f18,plain,(
% 2.61/0.76    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 2.61/0.76    inference(ennf_transformation,[],[f16])).
% 2.61/0.77  fof(f16,negated_conjecture,(
% 2.61/0.77    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.61/0.77    inference(negated_conjecture,[],[f15])).
% 2.61/0.77  fof(f15,conjecture,(
% 2.61/0.77    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.61/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 2.61/0.77  fof(f113,plain,(
% 2.61/0.77    ~spl8_5),
% 2.61/0.77    inference(avatar_split_clause,[],[f60,f110])).
% 2.61/0.77  fof(f60,plain,(
% 2.61/0.77    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.61/0.77    inference(definition_unfolding,[],[f25,f59,f30])).
% 2.61/0.77  fof(f25,plain,(
% 2.61/0.77    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 2.61/0.77    inference(cnf_transformation,[],[f19])).
% 2.61/0.77  fof(f98,plain,(
% 2.61/0.77    spl8_2),
% 2.61/0.77    inference(avatar_split_clause,[],[f24,f95])).
% 2.61/0.77  fof(f24,plain,(
% 2.61/0.77    r2_hidden(sK3,sK0)),
% 2.61/0.77    inference(cnf_transformation,[],[f19])).
% 2.61/0.77  fof(f93,plain,(
% 2.61/0.77    spl8_1),
% 2.61/0.77    inference(avatar_split_clause,[],[f22,f90])).
% 2.61/0.77  fof(f22,plain,(
% 2.61/0.77    r1_tarski(sK0,sK1)),
% 2.61/0.77    inference(cnf_transformation,[],[f19])).
% 2.61/0.77  % SZS output end Proof for theBenchmark
% 2.61/0.77  % (24026)------------------------------
% 2.61/0.77  % (24026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.61/0.77  % (24026)Termination reason: Refutation
% 2.61/0.77  
% 2.61/0.77  % (24026)Memory used [KB]: 12153
% 2.61/0.77  % (24026)Time elapsed: 0.359 s
% 2.61/0.77  % (24026)------------------------------
% 2.61/0.77  % (24026)------------------------------
% 2.61/0.77  % (24003)Success in time 0.405 s
%------------------------------------------------------------------------------
