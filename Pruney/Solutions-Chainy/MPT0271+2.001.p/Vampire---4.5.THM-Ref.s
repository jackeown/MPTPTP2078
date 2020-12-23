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
% DateTime   : Thu Dec  3 12:41:05 EST 2020

% Result     : Theorem 6.63s
% Output     : Refutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 160 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 ( 356 expanded)
%              Number of equality atoms :   57 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f1482,f1795,f1808,f1858,f1958,f2308,f2358])).

fof(f2358,plain,
    ( spl4_2
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f2354])).

fof(f2354,plain,
    ( $false
    | spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f99,f99,f116,f2307,f174])).

fof(f174,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_tarski(k5_xboole_0(X10,X11),X12)
      | ~ r2_hidden(X9,X11)
      | r2_hidden(X9,X12)
      | r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f61,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f2307,plain,
    ( r1_tarski(k5_xboole_0(sK1,k1_tarski(sK0)),sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f2305])).

fof(f2305,plain,
    ( spl4_20
  <=> r1_tarski(k5_xboole_0(sK1,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f116,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f112,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f112,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f66,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2308,plain,
    ( spl4_20
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f2290,f1955,f2305])).

fof(f1955,plain,
    ( spl4_11
  <=> k5_xboole_0(sK1,k1_tarski(sK0)) = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f2290,plain,
    ( r1_tarski(k5_xboole_0(sK1,k1_tarski(sK0)),sK1)
    | ~ spl4_11 ),
    inference(superposition,[],[f71,f1957])).

fof(f1957,plain,
    ( k5_xboole_0(sK1,k1_tarski(sK0)) = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f1955])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1958,plain,
    ( spl4_11
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1945,f1846,f1955])).

fof(f1846,plain,
    ( spl4_9
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1945,plain,
    ( k5_xboole_0(sK1,k1_tarski(sK0)) = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_9 ),
    inference(superposition,[],[f70,f1848])).

fof(f1848,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f1846])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1858,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1857,f1805,f1846])).

fof(f1805,plain,
    ( spl4_4
  <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1857,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1829,f265])).

fof(f265,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f209,f68])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f209,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f188,f103])).

fof(f103,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f68,f74])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f188,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f67,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1829,plain,
    ( k3_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f223,f1807])).

fof(f1807,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f1805])).

fof(f223,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f79,f67])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f1808,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f1803,f93,f1805])).

fof(f93,plain,
    ( spl4_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1803,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1796,f75])).

fof(f75,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1796,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_1 ),
    inference(superposition,[],[f69,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1795,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f1791,f1479,f97])).

fof(f1479,plain,
    ( spl4_3
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1791,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3 ),
    inference(resolution,[],[f1481,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1481,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f1479])).

fof(f1482,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f1477,f93,f1479])).

fof(f1477,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f1468])).

fof(f1468,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(superposition,[],[f95,f718])).

fof(f718,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f716,f76])).

fof(f716,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X1) = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f70,f714])).

fof(f714,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f235,f265])).

fof(f235,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(X2,k5_xboole_0(X1,X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f221,f68])).

fof(f221,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f79,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f95,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f101,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f48,f97,f93])).

fof(f48,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f100,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f97,f93])).

fof(f49,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (32236)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (32248)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (32240)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (32251)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (32230)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (32232)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (32243)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (32228)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (32239)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (32227)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (32229)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (32226)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (32250)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (32252)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (32253)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (32231)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (32255)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (32249)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (32254)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (32244)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (32233)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (32245)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (32247)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (32242)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (32238)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (32234)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (32241)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (32237)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (32246)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (32235)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 3.28/0.83  % (32231)Time limit reached!
% 3.28/0.83  % (32231)------------------------------
% 3.28/0.83  % (32231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.83  % (32231)Termination reason: Time limit
% 3.28/0.83  
% 3.28/0.83  % (32231)Memory used [KB]: 10106
% 3.28/0.83  % (32231)Time elapsed: 0.434 s
% 3.28/0.83  % (32231)------------------------------
% 3.28/0.83  % (32231)------------------------------
% 4.17/0.90  % (32238)Time limit reached!
% 4.17/0.90  % (32238)------------------------------
% 4.17/0.90  % (32238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.90  % (32238)Termination reason: Time limit
% 4.17/0.90  
% 4.17/0.90  % (32238)Memory used [KB]: 7675
% 4.17/0.90  % (32238)Time elapsed: 0.508 s
% 4.17/0.90  % (32238)------------------------------
% 4.17/0.90  % (32238)------------------------------
% 4.17/0.90  % (32243)Time limit reached!
% 4.17/0.90  % (32243)------------------------------
% 4.17/0.90  % (32243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.90  % (32227)Time limit reached!
% 4.17/0.90  % (32227)------------------------------
% 4.17/0.90  % (32227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.90  % (32227)Termination reason: Time limit
% 4.17/0.90  
% 4.17/0.90  % (32227)Memory used [KB]: 7419
% 4.17/0.90  % (32227)Time elapsed: 0.506 s
% 4.17/0.90  % (32227)------------------------------
% 4.17/0.90  % (32227)------------------------------
% 4.17/0.91  % (32226)Time limit reached!
% 4.17/0.91  % (32226)------------------------------
% 4.17/0.91  % (32226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.91  % (32226)Termination reason: Time limit
% 4.17/0.91  
% 4.17/0.91  % (32226)Memory used [KB]: 2430
% 4.17/0.91  % (32226)Time elapsed: 0.505 s
% 4.17/0.91  % (32226)------------------------------
% 4.17/0.91  % (32226)------------------------------
% 4.17/0.91  % (32243)Termination reason: Time limit
% 4.17/0.91  
% 4.17/0.91  % (32243)Memory used [KB]: 13944
% 4.17/0.91  % (32243)Time elapsed: 0.503 s
% 4.17/0.91  % (32243)------------------------------
% 4.17/0.91  % (32243)------------------------------
% 4.17/0.92  % (32236)Time limit reached!
% 4.17/0.92  % (32236)------------------------------
% 4.17/0.92  % (32236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.92  % (32236)Termination reason: Time limit
% 4.50/0.92  
% 4.50/0.92  % (32236)Memory used [KB]: 15607
% 4.50/0.92  % (32236)Time elapsed: 0.516 s
% 4.50/0.92  % (32236)------------------------------
% 4.50/0.92  % (32236)------------------------------
% 4.55/0.96  % (32256)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.55/1.00  % (32233)Time limit reached!
% 4.55/1.00  % (32233)------------------------------
% 4.55/1.00  % (32233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.00  % (32233)Termination reason: Time limit
% 4.55/1.00  % (32233)Termination phase: Saturation
% 4.55/1.00  
% 4.55/1.00  % (32233)Memory used [KB]: 10490
% 4.55/1.00  % (32233)Time elapsed: 0.600 s
% 4.55/1.00  % (32233)------------------------------
% 4.55/1.00  % (32233)------------------------------
% 4.55/1.00  % (32242)Time limit reached!
% 4.55/1.00  % (32242)------------------------------
% 4.55/1.00  % (32242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.00  % (32242)Termination reason: Time limit
% 4.55/1.00  
% 4.55/1.00  % (32242)Memory used [KB]: 15991
% 4.55/1.00  % (32242)Time elapsed: 0.607 s
% 4.55/1.00  % (32242)------------------------------
% 4.55/1.00  % (32242)------------------------------
% 5.03/1.02  % (32259)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.03/1.03  % (32258)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.03/1.04  % (32257)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.03/1.04  % (32254)Time limit reached!
% 5.03/1.04  % (32254)------------------------------
% 5.03/1.04  % (32254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.04  % (32254)Termination reason: Time limit
% 5.03/1.04  % (32254)Termination phase: Saturation
% 5.03/1.04  
% 5.03/1.04  % (32254)Memory used [KB]: 9594
% 5.03/1.04  % (32254)Time elapsed: 0.600 s
% 5.03/1.04  % (32254)------------------------------
% 5.03/1.04  % (32254)------------------------------
% 5.03/1.04  % (32260)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.68/1.08  % (32261)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.68/1.12  % (32262)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.68/1.14  % (32263)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.45/1.20  % (32247)Time limit reached!
% 6.45/1.20  % (32247)------------------------------
% 6.45/1.20  % (32247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.45/1.20  % (32247)Termination reason: Time limit
% 6.45/1.20  % (32247)Termination phase: Saturation
% 6.45/1.20  
% 6.45/1.20  % (32247)Memory used [KB]: 4605
% 6.45/1.20  % (32247)Time elapsed: 0.800 s
% 6.45/1.20  % (32247)------------------------------
% 6.45/1.20  % (32247)------------------------------
% 6.63/1.20  % (32264)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.63/1.22  % (32258)Refutation found. Thanks to Tanya!
% 6.63/1.22  % SZS status Theorem for theBenchmark
% 6.63/1.22  % SZS output start Proof for theBenchmark
% 6.85/1.22  fof(f2359,plain,(
% 6.85/1.22    $false),
% 6.85/1.22    inference(avatar_sat_refutation,[],[f100,f101,f1482,f1795,f1808,f1858,f1958,f2308,f2358])).
% 6.85/1.22  fof(f2358,plain,(
% 6.85/1.22    spl4_2 | ~spl4_20),
% 6.85/1.22    inference(avatar_contradiction_clause,[],[f2354])).
% 6.85/1.22  fof(f2354,plain,(
% 6.85/1.22    $false | (spl4_2 | ~spl4_20)),
% 6.85/1.22    inference(unit_resulting_resolution,[],[f99,f99,f116,f2307,f174])).
% 6.85/1.22  fof(f174,plain,(
% 6.85/1.22    ( ! [X12,X10,X11,X9] : (~r1_tarski(k5_xboole_0(X10,X11),X12) | ~r2_hidden(X9,X11) | r2_hidden(X9,X12) | r2_hidden(X9,X10)) )),
% 6.85/1.22    inference(resolution,[],[f61,f64])).
% 6.85/1.22  fof(f64,plain,(
% 6.85/1.22    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f47])).
% 6.85/1.22  fof(f47,plain,(
% 6.85/1.22    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.85/1.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 6.85/1.22  fof(f46,plain,(
% 6.85/1.22    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 6.85/1.22    introduced(choice_axiom,[])).
% 6.85/1.22  fof(f45,plain,(
% 6.85/1.22    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.85/1.22    inference(rectify,[],[f44])).
% 6.85/1.22  fof(f44,plain,(
% 6.85/1.22    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.85/1.22    inference(nnf_transformation,[],[f32])).
% 6.85/1.22  fof(f32,plain,(
% 6.85/1.22    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.85/1.22    inference(ennf_transformation,[],[f2])).
% 6.85/1.22  fof(f2,axiom,(
% 6.85/1.22    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 6.85/1.22  fof(f61,plain,(
% 6.85/1.22    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f42])).
% 6.85/1.22  fof(f42,plain,(
% 6.85/1.22    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 6.85/1.22    inference(nnf_transformation,[],[f31])).
% 6.85/1.22  fof(f31,plain,(
% 6.85/1.22    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 6.85/1.22    inference(ennf_transformation,[],[f4])).
% 6.85/1.22  fof(f4,axiom,(
% 6.85/1.22    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 6.85/1.22  fof(f2307,plain,(
% 6.85/1.22    r1_tarski(k5_xboole_0(sK1,k1_tarski(sK0)),sK1) | ~spl4_20),
% 6.85/1.22    inference(avatar_component_clause,[],[f2305])).
% 6.85/1.22  fof(f2305,plain,(
% 6.85/1.22    spl4_20 <=> r1_tarski(k5_xboole_0(sK1,k1_tarski(sK0)),sK1)),
% 6.85/1.22    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 6.85/1.22  fof(f116,plain,(
% 6.85/1.22    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 6.85/1.22    inference(resolution,[],[f112,f62])).
% 6.85/1.22  fof(f62,plain,(
% 6.85/1.22    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f43])).
% 6.85/1.22  fof(f43,plain,(
% 6.85/1.22    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 6.85/1.22    inference(nnf_transformation,[],[f23])).
% 6.85/1.22  fof(f23,axiom,(
% 6.85/1.22    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 6.85/1.22  fof(f112,plain,(
% 6.85/1.22    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 6.85/1.22    inference(duplicate_literal_removal,[],[f111])).
% 6.85/1.22  fof(f111,plain,(
% 6.85/1.22    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 6.85/1.22    inference(resolution,[],[f66,f65])).
% 6.85/1.22  fof(f65,plain,(
% 6.85/1.22    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f47])).
% 6.85/1.22  fof(f66,plain,(
% 6.85/1.22    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f47])).
% 6.85/1.22  fof(f99,plain,(
% 6.85/1.22    ~r2_hidden(sK0,sK1) | spl4_2),
% 6.85/1.22    inference(avatar_component_clause,[],[f97])).
% 6.85/1.22  fof(f97,plain,(
% 6.85/1.22    spl4_2 <=> r2_hidden(sK0,sK1)),
% 6.85/1.22    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 6.85/1.22  fof(f2308,plain,(
% 6.85/1.22    spl4_20 | ~spl4_11),
% 6.85/1.22    inference(avatar_split_clause,[],[f2290,f1955,f2305])).
% 6.85/1.22  fof(f1955,plain,(
% 6.85/1.22    spl4_11 <=> k5_xboole_0(sK1,k1_tarski(sK0)) = k4_xboole_0(sK1,k1_tarski(sK0))),
% 6.85/1.22    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 6.85/1.22  fof(f2290,plain,(
% 6.85/1.22    r1_tarski(k5_xboole_0(sK1,k1_tarski(sK0)),sK1) | ~spl4_11),
% 6.85/1.22    inference(superposition,[],[f71,f1957])).
% 6.85/1.22  fof(f1957,plain,(
% 6.85/1.22    k5_xboole_0(sK1,k1_tarski(sK0)) = k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_11),
% 6.85/1.22    inference(avatar_component_clause,[],[f1955])).
% 6.85/1.22  fof(f71,plain,(
% 6.85/1.22    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f8])).
% 6.85/1.22  fof(f8,axiom,(
% 6.85/1.22    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.85/1.22  fof(f1958,plain,(
% 6.85/1.22    spl4_11 | ~spl4_9),
% 6.85/1.22    inference(avatar_split_clause,[],[f1945,f1846,f1955])).
% 6.85/1.22  fof(f1846,plain,(
% 6.85/1.22    spl4_9 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 6.85/1.22    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 6.85/1.22  fof(f1945,plain,(
% 6.85/1.22    k5_xboole_0(sK1,k1_tarski(sK0)) = k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_9),
% 6.85/1.22    inference(superposition,[],[f70,f1848])).
% 6.85/1.22  fof(f1848,plain,(
% 6.85/1.22    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_9),
% 6.85/1.22    inference(avatar_component_clause,[],[f1846])).
% 6.85/1.22  fof(f70,plain,(
% 6.85/1.22    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.85/1.22    inference(cnf_transformation,[],[f5])).
% 6.85/1.22  fof(f5,axiom,(
% 6.85/1.22    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.85/1.22  fof(f1858,plain,(
% 6.85/1.22    spl4_9 | ~spl4_4),
% 6.85/1.22    inference(avatar_split_clause,[],[f1857,f1805,f1846])).
% 6.85/1.22  fof(f1805,plain,(
% 6.85/1.22    spl4_4 <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 6.85/1.22    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 6.85/1.22  fof(f1857,plain,(
% 6.85/1.22    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_4),
% 6.85/1.22    inference(forward_demodulation,[],[f1829,f265])).
% 6.85/1.22  fof(f265,plain,(
% 6.85/1.22    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 6.85/1.22    inference(superposition,[],[f209,f68])).
% 6.85/1.22  fof(f68,plain,(
% 6.85/1.22    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f1])).
% 6.85/1.22  fof(f1,axiom,(
% 6.85/1.22    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 6.85/1.22  fof(f209,plain,(
% 6.85/1.22    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 6.85/1.22    inference(forward_demodulation,[],[f188,f103])).
% 6.85/1.22  fof(f103,plain,(
% 6.85/1.22    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 6.85/1.22    inference(superposition,[],[f68,f74])).
% 6.85/1.22  fof(f74,plain,(
% 6.85/1.22    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.85/1.22    inference(cnf_transformation,[],[f10])).
% 6.85/1.22  fof(f10,axiom,(
% 6.85/1.22    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 6.85/1.22  fof(f188,plain,(
% 6.85/1.22    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 6.85/1.22    inference(superposition,[],[f67,f76])).
% 6.85/1.22  fof(f76,plain,(
% 6.85/1.22    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f12])).
% 6.85/1.22  fof(f12,axiom,(
% 6.85/1.22    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 6.85/1.22  fof(f67,plain,(
% 6.85/1.22    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 6.85/1.22    inference(cnf_transformation,[],[f11])).
% 6.85/1.22  fof(f11,axiom,(
% 6.85/1.22    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 6.85/1.22  fof(f1829,plain,(
% 6.85/1.22    k3_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),sK1)) | ~spl4_4),
% 6.85/1.22    inference(superposition,[],[f223,f1807])).
% 6.85/1.22  fof(f1807,plain,(
% 6.85/1.22    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_4),
% 6.85/1.22    inference(avatar_component_clause,[],[f1805])).
% 6.85/1.22  fof(f223,plain,(
% 6.85/1.22    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))) )),
% 6.85/1.22    inference(superposition,[],[f79,f67])).
% 6.85/1.22  fof(f79,plain,(
% 6.85/1.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 6.85/1.22    inference(cnf_transformation,[],[f13])).
% 6.85/1.22  fof(f13,axiom,(
% 6.85/1.22    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 6.85/1.22  fof(f1808,plain,(
% 6.85/1.22    spl4_4 | ~spl4_1),
% 6.85/1.22    inference(avatar_split_clause,[],[f1803,f93,f1805])).
% 6.85/1.22  fof(f93,plain,(
% 6.85/1.22    spl4_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 6.85/1.22    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 6.85/1.22  fof(f1803,plain,(
% 6.85/1.22    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_1),
% 6.85/1.22    inference(forward_demodulation,[],[f1796,f75])).
% 6.85/1.22  fof(f75,plain,(
% 6.85/1.22    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.85/1.22    inference(cnf_transformation,[],[f7])).
% 6.85/1.22  fof(f7,axiom,(
% 6.85/1.22    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 6.85/1.22  fof(f1796,plain,(
% 6.85/1.22    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) | ~spl4_1),
% 6.85/1.22    inference(superposition,[],[f69,f94])).
% 6.85/1.22  fof(f94,plain,(
% 6.85/1.22    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 6.85/1.22    inference(avatar_component_clause,[],[f93])).
% 6.85/1.22  fof(f69,plain,(
% 6.85/1.22    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.85/1.22    inference(cnf_transformation,[],[f9])).
% 6.85/1.22  fof(f9,axiom,(
% 6.85/1.22    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 6.85/1.22  fof(f1795,plain,(
% 6.85/1.22    ~spl4_2 | spl4_3),
% 6.85/1.22    inference(avatar_split_clause,[],[f1791,f1479,f97])).
% 6.85/1.22  fof(f1479,plain,(
% 6.85/1.22    spl4_3 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 6.85/1.22    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 6.85/1.22  fof(f1791,plain,(
% 6.85/1.22    ~r2_hidden(sK0,sK1) | spl4_3),
% 6.85/1.22    inference(resolution,[],[f1481,f63])).
% 6.85/1.22  fof(f63,plain,(
% 6.85/1.22    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f43])).
% 6.85/1.22  fof(f1481,plain,(
% 6.85/1.22    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_3),
% 6.85/1.22    inference(avatar_component_clause,[],[f1479])).
% 6.85/1.22  fof(f1482,plain,(
% 6.85/1.22    ~spl4_3 | spl4_1),
% 6.85/1.22    inference(avatar_split_clause,[],[f1477,f93,f1479])).
% 6.85/1.22  fof(f1477,plain,(
% 6.85/1.22    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 6.85/1.22    inference(trivial_inequality_removal,[],[f1468])).
% 6.85/1.22  fof(f1468,plain,(
% 6.85/1.22    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 6.85/1.22    inference(superposition,[],[f95,f718])).
% 6.85/1.22  fof(f718,plain,(
% 6.85/1.22    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 6.85/1.22    inference(forward_demodulation,[],[f716,f76])).
% 6.85/1.22  fof(f716,plain,(
% 6.85/1.22    ( ! [X2,X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 6.85/1.22    inference(superposition,[],[f70,f714])).
% 6.85/1.22  fof(f714,plain,(
% 6.85/1.22    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) )),
% 6.85/1.22    inference(forward_demodulation,[],[f235,f265])).
% 6.85/1.22  fof(f235,plain,(
% 6.85/1.22    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) | ~r1_tarski(X1,X2)) )),
% 6.85/1.22    inference(forward_demodulation,[],[f221,f68])).
% 6.85/1.22  fof(f221,plain,(
% 6.85/1.22    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X2) | ~r1_tarski(X1,X2)) )),
% 6.85/1.22    inference(superposition,[],[f79,f80])).
% 6.85/1.22  fof(f80,plain,(
% 6.85/1.22    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 6.85/1.22    inference(cnf_transformation,[],[f33])).
% 6.85/1.22  fof(f33,plain,(
% 6.85/1.22    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.85/1.22    inference(ennf_transformation,[],[f6])).
% 6.85/1.22  fof(f6,axiom,(
% 6.85/1.22    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 6.85/1.22  fof(f95,plain,(
% 6.85/1.22    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl4_1),
% 6.85/1.22    inference(avatar_component_clause,[],[f93])).
% 6.85/1.22  fof(f101,plain,(
% 6.85/1.22    spl4_1 | spl4_2),
% 6.85/1.22    inference(avatar_split_clause,[],[f48,f97,f93])).
% 6.85/1.22  fof(f48,plain,(
% 6.85/1.22    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 6.85/1.22    inference(cnf_transformation,[],[f36])).
% 6.85/1.22  fof(f36,plain,(
% 6.85/1.22    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 6.85/1.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).
% 6.85/1.22  fof(f35,plain,(
% 6.85/1.22    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 6.85/1.22    introduced(choice_axiom,[])).
% 6.85/1.22  fof(f34,plain,(
% 6.85/1.22    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 6.85/1.22    inference(nnf_transformation,[],[f29])).
% 6.85/1.22  fof(f29,plain,(
% 6.85/1.22    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 6.85/1.22    inference(ennf_transformation,[],[f27])).
% 6.85/1.22  fof(f27,negated_conjecture,(
% 6.85/1.22    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.85/1.22    inference(negated_conjecture,[],[f26])).
% 6.85/1.22  fof(f26,conjecture,(
% 6.85/1.22    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.85/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 6.85/1.22  fof(f100,plain,(
% 6.85/1.22    ~spl4_1 | ~spl4_2),
% 6.85/1.22    inference(avatar_split_clause,[],[f49,f97,f93])).
% 6.85/1.22  fof(f49,plain,(
% 6.85/1.22    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 6.85/1.22    inference(cnf_transformation,[],[f36])).
% 6.85/1.22  % SZS output end Proof for theBenchmark
% 6.85/1.22  % (32258)------------------------------
% 6.85/1.22  % (32258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.85/1.22  % (32258)Termination reason: Refutation
% 6.85/1.22  
% 6.85/1.22  % (32258)Memory used [KB]: 8059
% 6.85/1.22  % (32258)Time elapsed: 0.288 s
% 6.85/1.22  % (32258)------------------------------
% 6.85/1.22  % (32258)------------------------------
% 6.85/1.23  % (32225)Success in time 0.869 s
%------------------------------------------------------------------------------
