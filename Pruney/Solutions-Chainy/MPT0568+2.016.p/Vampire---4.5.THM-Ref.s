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
% DateTime   : Thu Dec  3 12:50:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :  130 ( 169 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f43,f47,f51,f55,f59,f72,f75,f85,f92,f98])).

fof(f98,plain,
    ( spl1_1
    | ~ spl1_14 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl1_1
    | ~ spl1_14 ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_14 ),
    inference(superposition,[],[f27,f90])).

fof(f90,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl1_14
  <=> ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f27,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f92,plain,
    ( spl1_14
    | ~ spl1_5
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f87,f83,f45,f89])).

fof(f45,plain,
    ( spl1_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f83,plain,
    ( spl1_13
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f87,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_5
    | ~ spl1_13 ),
    inference(superposition,[],[f46,f84])).

fof(f84,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f46,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f85,plain,
    ( spl1_13
    | ~ spl1_8
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f77,f70,f57,f83])).

fof(f57,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f70,plain,
    ( spl1_11
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f77,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl1_8
    | ~ spl1_11 ),
    inference(resolution,[],[f58,f71])).

fof(f71,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f70])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f75,plain,
    ( ~ spl1_2
    | ~ spl1_6
    | spl1_10 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_6
    | spl1_10 ),
    inference(subsumption_resolution,[],[f73,f32])).

fof(f32,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f73,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_6
    | spl1_10 ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f68,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl1_10
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f72,plain,
    ( ~ spl1_10
    | spl1_11
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f64,f53,f40,f70,f66])).

fof(f40,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f53,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f64,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(superposition,[],[f54,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f59,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f55,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f51,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f47,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f43,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f33,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f28,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (11716)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (11716)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f28,f33,f43,f47,f51,f55,f59,f72,f75,f85,f92,f98])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    spl1_1 | ~spl1_14),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f97])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    $false | (spl1_1 | ~spl1_14)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f93])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_14)),
% 0.21/0.42    inference(superposition,[],[f27,f90])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    ( ! [X1] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) ) | ~spl1_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl1_14 <=> ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    spl1_14 | ~spl1_5 | ~spl1_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f87,f83,f45,f89])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl1_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl1_13 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl1_5 | ~spl1_13)),
% 0.21/0.42    inference(superposition,[],[f46,f84])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)) ) | ~spl1_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f83])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f45])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl1_13 | ~spl1_8 | ~spl1_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f77,f70,f57,f83])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl1_8 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl1_11 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)) ) | (~spl1_8 | ~spl1_11)),
% 0.21/0.42    inference(resolution,[],[f58,f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl1_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ~spl1_2 | ~spl1_6 | spl1_10),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    $false | (~spl1_2 | ~spl1_6 | spl1_10)),
% 0.21/0.42    inference(subsumption_resolution,[],[f73,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    ~v1_xboole_0(k1_xboole_0) | (~spl1_6 | spl1_10)),
% 0.21/0.42    inference(resolution,[],[f68,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl1_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    ~v1_relat_1(k1_xboole_0) | spl1_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl1_10 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    ~spl1_10 | spl1_11 | ~spl1_4 | ~spl1_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f53,f40,f70,f66])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl1_7 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_7)),
% 0.21/0.42    inference(superposition,[],[f54,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl1_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl1_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f57])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl1_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f53])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f49])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl1_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f45])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl1_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f40])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ~spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f25])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (11716)------------------------------
% 0.21/0.42  % (11716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (11716)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (11716)Memory used [KB]: 10618
% 0.21/0.42  % (11716)Time elapsed: 0.006 s
% 0.21/0.42  % (11716)------------------------------
% 0.21/0.42  % (11716)------------------------------
% 0.21/0.42  % (11710)Success in time 0.063 s
%------------------------------------------------------------------------------
