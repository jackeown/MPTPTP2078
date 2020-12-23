%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t13_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:24 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :  166 ( 253 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f77,f78,f87,f96,f105,f113,f188,f192,f200,f204])).

fof(f204,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f201,f68])).

fof(f68,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f201,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f53,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t13_ordinal1.p',d3_xboole_0)).

fof(f53,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_1
  <=> ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f200,plain,
    ( ~ spl4_17
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f193,f67,f198])).

fof(f198,plain,
    ( spl4_17
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f193,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f68,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t13_ordinal1.p',antisymmetry_r2_hidden)).

fof(f192,plain,
    ( spl4_3
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f189,f59])).

fof(f59,plain,
    ( sK0 != sK1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_3
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f189,plain,
    ( sK0 = sK1
    | ~ spl4_14 ),
    inference(resolution,[],[f187,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t13_ordinal1.p',d1_tarski)).

fof(f187,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_14
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f188,plain,
    ( spl4_14
    | ~ spl4_0
    | spl4_5 ),
    inference(avatar_split_clause,[],[f181,f64,f55,f186])).

fof(f55,plain,
    ( spl4_0
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f64,plain,
    ( spl4_5
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f181,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl4_0
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f173,f65])).

fof(f65,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f173,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | r2_hidden(sK0,sK1)
    | ~ spl4_0 ),
    inference(resolution,[],[f47,f56])).

fof(f56,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f55])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f113,plain,
    ( ~ spl4_13
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f106,f72,f111])).

fof(f111,plain,
    ( spl4_13
  <=> ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f72,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f106,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f73,f28])).

fof(f73,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f105,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f50,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f100,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f45,f76])).

fof(f76,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_7
  <=> ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,
    ( ~ spl4_11
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f88,f55,f94])).

fof(f94,plain,
    ( spl4_11
  <=> ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f88,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ spl4_0 ),
    inference(resolution,[],[f28,f56])).

fof(f87,plain,
    ( ~ spl4_9
    | ~ spl4_2
    | spl4_5 ),
    inference(avatar_split_clause,[],[f80,f64,f61,f85])).

fof(f85,plain,
    ( spl4_9
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f61,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f65,f62])).

fof(f62,plain,
    ( sK0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f78,plain,
    ( ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f44,f64,f52])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t13_ordinal1.p',d1_ordinal1)).

fof(f25,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t13_ordinal1.p',t13_ordinal1)).

fof(f77,plain,
    ( ~ spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f70,f58,f75])).

fof(f70,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(inner_rewriting,[],[f43])).

fof(f43,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f26,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,
    ( spl4_0
    | spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f42,f67,f61,f55])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f27,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
