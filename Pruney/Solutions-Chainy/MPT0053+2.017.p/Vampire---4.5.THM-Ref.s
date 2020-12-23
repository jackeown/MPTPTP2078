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
% DateTime   : Thu Dec  3 12:29:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :  112 ( 171 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f41,f46,f56,f61,f66,f97,f155])).

fof(f155,plain,
    ( spl2_1
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl2_1
    | ~ spl2_13 ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_1
    | ~ spl2_13 ),
    inference(superposition,[],[f20,f96])).

fof(f96,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_13
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f20,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f97,plain,
    ( spl2_13
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f93,f64,f54,f39,f95])).

fof(f39,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f54,plain,
    ( spl2_9
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f64,plain,
    ( spl2_11
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f93,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f77,f65])).

fof(f65,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f64])).

fof(f77,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f40,f55])).

fof(f55,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f54])).

fof(f40,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f66,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f62,f59,f31,f64])).

fof(f31,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_10
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f62,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(resolution,[],[f60,f32])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f60,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f57,f54,f27,f59])).

fof(f27,plain,
    ( spl2_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(superposition,[],[f28,f55])).

fof(f28,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f56,plain,
    ( spl2_9
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f48,f44,f31,f54])).

fof(f44,plain,
    ( spl2_7
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f48,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f44])).

fof(f46,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f42,f27,f23,f44])).

fof(f23,plain,
    ( spl2_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f42,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f28,f24])).

fof(f24,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f41,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f33,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f29,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f25,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f21,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))
   => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:30:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (6384)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (6387)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.42  % (6384)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f157,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f41,f46,f56,f61,f66,f97,f155])).
% 0.22/0.42  fof(f155,plain,(
% 0.22/0.42    spl2_1 | ~spl2_13),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.42  fof(f154,plain,(
% 0.22/0.42    $false | (spl2_1 | ~spl2_13)),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f153])).
% 0.22/0.42  fof(f153,plain,(
% 0.22/0.42    k1_xboole_0 != k1_xboole_0 | (spl2_1 | ~spl2_13)),
% 0.22/0.42    inference(superposition,[],[f20,f96])).
% 0.22/0.42  fof(f96,plain,(
% 0.22/0.42    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | ~spl2_13),
% 0.22/0.42    inference(avatar_component_clause,[],[f95])).
% 0.22/0.42  fof(f95,plain,(
% 0.22/0.42    spl2_13 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    spl2_1 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.42  fof(f97,plain,(
% 0.22/0.42    spl2_13 | ~spl2_6 | ~spl2_9 | ~spl2_11),
% 0.22/0.42    inference(avatar_split_clause,[],[f93,f64,f54,f39,f95])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    spl2_6 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    spl2_9 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    spl2_11 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.42  fof(f93,plain,(
% 0.22/0.42    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_6 | ~spl2_9 | ~spl2_11)),
% 0.22/0.42    inference(forward_demodulation,[],[f77,f65])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_11),
% 0.22/0.42    inference(avatar_component_clause,[],[f64])).
% 0.22/0.42  fof(f77,plain,(
% 0.22/0.42    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) ) | (~spl2_6 | ~spl2_9)),
% 0.22/0.42    inference(superposition,[],[f40,f55])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl2_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f54])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f39])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    spl2_11 | ~spl2_4 | ~spl2_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f62,f59,f31,f64])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    spl2_4 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    spl2_10 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_4 | ~spl2_10)),
% 0.22/0.42    inference(resolution,[],[f60,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f31])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f59])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    spl2_10 | ~spl2_3 | ~spl2_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f57,f54,f27,f59])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    spl2_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl2_3 | ~spl2_9)),
% 0.22/0.42    inference(superposition,[],[f28,f55])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f27])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    spl2_9 | ~spl2_4 | ~spl2_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f48,f44,f31,f54])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    spl2_7 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl2_4 | ~spl2_7)),
% 0.22/0.42    inference(resolution,[],[f32,f45])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl2_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f44])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    spl2_7 | ~spl2_2 | ~spl2_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f42,f27,f23,f44])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    spl2_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.42    inference(superposition,[],[f28,f24])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f23])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    spl2_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f39])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl2_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f31])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.42    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f13,f27])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f12,f23])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ~spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f11,f18])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (6384)------------------------------
% 0.22/0.43  % (6384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (6384)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (6384)Memory used [KB]: 10618
% 0.22/0.43  % (6384)Time elapsed: 0.007 s
% 0.22/0.43  % (6384)------------------------------
% 0.22/0.43  % (6384)------------------------------
% 0.22/0.43  % (6378)Success in time 0.066 s
%------------------------------------------------------------------------------
