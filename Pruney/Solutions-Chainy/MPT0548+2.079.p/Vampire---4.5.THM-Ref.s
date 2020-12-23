%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 125 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f46,f52,f58,f66,f75])).

fof(f75,plain,
    ( spl1_1
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl1_1
    | ~ spl1_8 ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_8 ),
    inference(superposition,[],[f24,f65])).

fof(f65,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl1_8
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f24,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f66,plain,
    ( spl1_8
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f62,f56,f43,f32,f64])).

fof(f32,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f43,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f56,plain,
    ( spl1_7
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f62,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f61,f34])).

fof(f34,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f61,plain,
    ( ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f59,f45])).

fof(f45,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f59,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_7 ),
    inference(superposition,[],[f20,f57])).

fof(f57,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f58,plain,
    ( spl1_7
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f54,f50,f56])).

fof(f50,plain,
    ( spl1_6
  <=> ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f54,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_6 ),
    inference(resolution,[],[f51,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f51,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,
    ( spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f48,f43,f50])).

fof(f48,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_5 ),
    inference(resolution,[],[f45,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f46,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f41,f27,f43])).

fof(f27,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f41,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(superposition,[],[f17,f29])).

fof(f29,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f35,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f30,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f25,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.42  % (2638)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.42  % (2638)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f76,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f25,f30,f35,f46,f52,f58,f66,f75])).
% 0.22/0.42  fof(f75,plain,(
% 0.22/0.42    spl1_1 | ~spl1_8),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f74])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    $false | (spl1_1 | ~spl1_8)),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f73])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_8)),
% 0.22/0.42    inference(superposition,[],[f24,f65])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl1_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f64])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    spl1_8 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    spl1_8 | ~spl1_3 | ~spl1_5 | ~spl1_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f62,f56,f43,f32,f64])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    spl1_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    spl1_7 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl1_3 | ~spl1_5 | ~spl1_7)),
% 0.22/0.42    inference(forward_demodulation,[],[f61,f34])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f32])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl1_5 | ~spl1_7)),
% 0.22/0.42    inference(subsumption_resolution,[],[f59,f45])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f43])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_7),
% 0.22/0.42    inference(superposition,[],[f20,f57])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl1_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f56])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    spl1_7 | ~spl1_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f54,f50,f56])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl1_6 <=> ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl1_6),
% 0.22/0.42    inference(resolution,[],[f51,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f50])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    spl1_6 | ~spl1_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f48,f43,f50])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_5),
% 0.22/0.42    inference(resolution,[],[f45,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    spl1_5 | ~spl1_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f41,f27,f43])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.22/0.42    inference(superposition,[],[f17,f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f27])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl1_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f32])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl1_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f14,f27])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ~spl1_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f13,f22])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,negated_conjecture,(
% 0.22/0.42    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    inference(negated_conjecture,[],[f7])).
% 0.22/0.42  fof(f7,conjecture,(
% 0.22/0.42    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (2638)------------------------------
% 0.22/0.42  % (2638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (2638)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (2638)Memory used [KB]: 10618
% 0.22/0.42  % (2638)Time elapsed: 0.006 s
% 0.22/0.42  % (2638)------------------------------
% 0.22/0.42  % (2638)------------------------------
% 0.22/0.42  % (2644)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (2633)Success in time 0.066 s
%------------------------------------------------------------------------------
