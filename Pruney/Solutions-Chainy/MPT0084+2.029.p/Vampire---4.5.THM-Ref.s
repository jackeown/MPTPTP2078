%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 191 expanded)
%              Number of leaves         :   30 (  89 expanded)
%              Depth                    :    7
%              Number of atoms          :  255 ( 437 expanded)
%              Number of equality atoms :   49 ( 101 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f53,f58,f62,f66,f70,f77,f82,f87,f93,f98,f102,f124,f128,f194,f284,f333,f340])).

fof(f340,plain,
    ( spl4_1
    | ~ spl4_16
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl4_1
    | ~ spl4_16
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f334,f39])).

fof(f39,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f334,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_16
    | ~ spl4_33 ),
    inference(resolution,[],[f332,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f332,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl4_33
  <=> ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f333,plain,
    ( spl4_33
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f308,f282,f192,f122,f96,f90,f331])).

fof(f90,plain,
    ( spl4_12
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f96,plain,
    ( spl4_13
  <=> ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f122,plain,
    ( spl4_15
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f192,plain,
    ( spl4_24
  <=> ! [X1,X0,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f282,plain,
    ( spl4_29
  <=> ! [X16,X15] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = X15 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f308,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f272,f289])).

fof(f289,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_15
    | ~ spl4_29 ),
    inference(superposition,[],[f283,f123])).

fof(f123,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f283,plain,
    ( ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = X15
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f282])).

fof(f272,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)))
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f97,f239])).

fof(f239,plain,
    ( ! [X19] : k4_xboole_0(sK0,k4_xboole_0(X19,k4_xboole_0(X19,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X19),k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(superposition,[],[f193,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f193,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f192])).

fof(f97,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f284,plain,
    ( spl4_29
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f259,f192,f80,f51,f282])).

fof(f51,plain,
    ( spl4_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f80,plain,
    ( spl4_10
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f259,plain,
    ( ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = X15
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f258,f52])).

fof(f52,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f258,plain,
    ( ! [X15,X16] : k4_xboole_0(X15,k1_xboole_0) = k2_xboole_0(X15,k4_xboole_0(X15,X16))
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f229,f81])).

fof(f81,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f229,plain,
    ( ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X16))) = k2_xboole_0(X15,k4_xboole_0(X15,X16))
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(superposition,[],[f193,f52])).

fof(f194,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f35,f192])).

% (7405)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f128,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f34,f126])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f26])).

% (7408)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f124,plain,
    ( spl4_15
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f111,f100,f80,f51,f122])).

fof(f100,plain,
    ( spl4_14
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f111,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f103,f81])).

fof(f103,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(superposition,[],[f101,f52])).

fof(f101,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f32,f100])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f26,f26])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f98,plain,
    ( spl4_13
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f94,f68,f55,f96])).

fof(f55,plain,
    ( spl4_5
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f94,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f93,plain,
    ( spl4_12
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f88,f84,f60,f90])).

fof(f60,plain,
    ( spl4_6
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f84,plain,
    ( spl4_11
  <=> sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f88,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(superposition,[],[f61,f86])).

fof(f86,plain,
    ( sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f61,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f87,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f71,f64,f42,f84])).

fof(f42,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f71,plain,
    ( sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0))
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f82,plain,
    ( spl4_10
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f78,f75,f60,f80])).

fof(f75,plain,
    ( spl4_9
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f78,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(superposition,[],[f61,f76])).

fof(f76,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f73,f64,f51,f47,f75])).

fof(f47,plain,
    ( spl4_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f72,f52])).

fof(f72,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f65,f48])).

fof(f48,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f70,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f62,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f58,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f21,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f53,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

% (7415)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f45,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:29:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (7411)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (7403)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (7404)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (7407)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (7402)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (7406)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (7400)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (7407)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f341,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f40,f45,f49,f53,f58,f62,f66,f70,f77,f82,f87,f93,f98,f102,f124,f128,f194,f284,f333,f340])).
% 0.22/0.48  fof(f340,plain,(
% 0.22/0.48    spl4_1 | ~spl4_16 | ~spl4_33),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f339])).
% 0.22/0.48  fof(f339,plain,(
% 0.22/0.48    $false | (spl4_1 | ~spl4_16 | ~spl4_33)),
% 0.22/0.48    inference(subsumption_resolution,[],[f334,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,sK1) | spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f334,plain,(
% 0.22/0.48    r1_xboole_0(sK0,sK1) | (~spl4_16 | ~spl4_33)),
% 0.22/0.48    inference(resolution,[],[f332,f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) ) | ~spl4_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl4_16 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.48  fof(f332,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl4_33),
% 0.22/0.48    inference(avatar_component_clause,[],[f331])).
% 0.22/0.48  fof(f331,plain,(
% 0.22/0.48    spl4_33 <=> ! [X0] : ~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.48  fof(f333,plain,(
% 0.22/0.48    spl4_33 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_24 | ~spl4_29),
% 0.22/0.48    inference(avatar_split_clause,[],[f308,f282,f192,f122,f96,f90,f331])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl4_12 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl4_13 <=> ! [X0] : ~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    spl4_15 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    spl4_24 <=> ! [X1,X0,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.48  fof(f282,plain,(
% 0.22/0.48    spl4_29 <=> ! [X16,X15] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = X15),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.48  fof(f308,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | (~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_24 | ~spl4_29)),
% 0.22/0.48    inference(backward_demodulation,[],[f272,f289])).
% 0.22/0.48  fof(f289,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl4_15 | ~spl4_29)),
% 0.22/0.48    inference(superposition,[],[f283,f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl4_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f122])).
% 0.22/0.48  fof(f283,plain,(
% 0.22/0.48    ( ! [X15,X16] : (k2_xboole_0(X15,k4_xboole_0(X15,X16)) = X15) ) | ~spl4_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f282])).
% 0.22/0.48  fof(f272,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)))) ) | (~spl4_12 | ~spl4_13 | ~spl4_24)),
% 0.22/0.48    inference(backward_demodulation,[],[f97,f239])).
% 0.22/0.48  fof(f239,plain,(
% 0.22/0.48    ( ! [X19] : (k4_xboole_0(sK0,k4_xboole_0(X19,k4_xboole_0(X19,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X19),k1_xboole_0)) ) | (~spl4_12 | ~spl4_24)),
% 0.22/0.48    inference(superposition,[],[f193,f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl4_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f90])).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) | ~spl4_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f192])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) ) | ~spl4_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f96])).
% 0.22/0.48  fof(f284,plain,(
% 0.22/0.48    spl4_29 | ~spl4_4 | ~spl4_10 | ~spl4_24),
% 0.22/0.48    inference(avatar_split_clause,[],[f259,f192,f80,f51,f282])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl4_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl4_10 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.48  fof(f259,plain,(
% 0.22/0.48    ( ! [X15,X16] : (k2_xboole_0(X15,k4_xboole_0(X15,X16)) = X15) ) | (~spl4_4 | ~spl4_10 | ~spl4_24)),
% 0.22/0.48    inference(forward_demodulation,[],[f258,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f51])).
% 0.22/0.48  fof(f258,plain,(
% 0.22/0.48    ( ! [X15,X16] : (k4_xboole_0(X15,k1_xboole_0) = k2_xboole_0(X15,k4_xboole_0(X15,X16))) ) | (~spl4_4 | ~spl4_10 | ~spl4_24)),
% 0.22/0.48    inference(forward_demodulation,[],[f229,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl4_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f80])).
% 0.22/0.48  fof(f229,plain,(
% 0.22/0.48    ( ! [X15,X16] : (k4_xboole_0(X15,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X16))) = k2_xboole_0(X15,k4_xboole_0(X15,X16))) ) | (~spl4_4 | ~spl4_24)),
% 0.22/0.48    inference(superposition,[],[f193,f52])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    spl4_24),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f192])).
% 0.22/0.48  % (7405)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f30,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl4_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f126])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f27,f26])).
% 0.22/0.48  % (7408)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl4_15 | ~spl4_4 | ~spl4_10 | ~spl4_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f111,f100,f80,f51,f122])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    spl4_14 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl4_4 | ~spl4_10 | ~spl4_14)),
% 0.22/0.48    inference(forward_demodulation,[],[f103,f81])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) ) | (~spl4_4 | ~spl4_14)),
% 0.22/0.48    inference(superposition,[],[f101,f52])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl4_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f100])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl4_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f100])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f25,f26,f26])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    spl4_13 | ~spl4_5 | ~spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f94,f68,f55,f96])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl4_5 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl4_8 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) ) | (~spl4_5 | ~spl4_8)),
% 0.22/0.48    inference(resolution,[],[f69,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f55])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl4_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl4_12 | ~spl4_6 | ~spl4_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f88,f84,f60,f90])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl4_6 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl4_11 <=> sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK2) | (~spl4_6 | ~spl4_11)),
% 0.22/0.48    inference(superposition,[],[f61,f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0)) | ~spl4_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f60])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl4_11 | ~spl4_2 | ~spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f71,f64,f42,f84])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl4_2 <=> r1_tarski(sK0,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl4_7 <=> ! [X1,X0] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0)) | (~spl4_2 | ~spl4_7)),
% 0.22/0.48    inference(resolution,[],[f65,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    r1_tarski(sK0,sK2) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) ) | ~spl4_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl4_10 | ~spl4_6 | ~spl4_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f78,f75,f60,f80])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl4_9 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl4_6 | ~spl4_9)),
% 0.22/0.48    inference(superposition,[],[f61,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl4_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f75])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl4_9 | ~spl4_3 | ~spl4_4 | ~spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f73,f64,f51,f47,f75])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    spl4_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.22/0.48    inference(forward_demodulation,[],[f72,f52])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) ) | (~spl4_3 | ~spl4_7)),
% 0.22/0.48    inference(resolution,[],[f65,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f47])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f68])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f28,f26])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f64])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f60])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f31,f55])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.22/0.48    inference(definition_unfolding,[],[f21,f26])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f23,f51])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f47])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  % (7415)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    r1_tarski(sK0,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ~spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f37])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7407)------------------------------
% 0.22/0.48  % (7407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7407)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7407)Memory used [KB]: 6396
% 0.22/0.48  % (7407)Time elapsed: 0.014 s
% 0.22/0.48  % (7407)------------------------------
% 0.22/0.48  % (7407)------------------------------
% 0.22/0.48  % (7410)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (7399)Success in time 0.123 s
%------------------------------------------------------------------------------
