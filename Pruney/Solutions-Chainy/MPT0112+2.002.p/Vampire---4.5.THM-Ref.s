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
% DateTime   : Thu Dec  3 12:32:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  91 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :    6
%              Number of atoms          :  127 ( 191 expanded)
%              Number of equality atoms :   29 (  52 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f32,f36,f40,f44,f48,f59,f76,f77,f102,f117])).

fof(f117,plain,
    ( spl2_9
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl2_9
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f114,f58])).

fof(f58,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f114,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(superposition,[],[f74,f101])).

fof(f101,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_13
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f74,plain,
    ( ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_11
  <=> ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f102,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f97,f67,f42,f38,f20,f99])).

fof(f20,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f38,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f42,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f67,plain,
    ( spl2_10
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f97,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f96,f68])).

fof(f68,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f96,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f91,f39])).

fof(f39,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f91,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f43,f22])).

fof(f22,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f43,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f77,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f65,f38,f34,f73])).

fof(f34,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f65,plain,
    ( ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f35,f39])).

fof(f35,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f76,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f64,f38,f30,f67])).

fof(f30,plain,
    ( spl2_3
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f64,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f31,f39])).

fof(f31,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f59,plain,
    ( ~ spl2_9
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f54,f46,f25,f56])).

fof(f25,plain,
    ( spl2_2
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f46,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( ~ r2_xboole_0(X1,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f54,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(resolution,[],[f47,f27])).

fof(f27,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X1,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f48,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f44,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f40,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f36,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f32,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f28,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f23,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f13,f20])).

fof(f13,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:08:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.41  % (21640)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (21642)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (21643)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (21641)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (21641)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f23,f28,f32,f36,f40,f44,f48,f59,f76,f77,f102,f117])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    spl2_9 | ~spl2_11 | ~spl2_13),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    $false | (spl2_9 | ~spl2_11 | ~spl2_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f114,f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ~r1_tarski(sK1,sK0) | spl2_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl2_9 <=> r1_tarski(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    r1_tarski(sK1,sK0) | (~spl2_11 | ~spl2_13)),
% 0.21/0.42    inference(superposition,[],[f74,f101])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    sK0 = k2_xboole_0(sK0,sK1) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f99])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    spl2_13 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) ) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f73])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    spl2_11 <=> ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X2,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    spl2_13 | ~spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f97,f67,f42,f38,f20,f99])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    spl2_1 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    spl2_10 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    sK0 = k2_xboole_0(sK0,sK1) | (~spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_10)),
% 0.21/0.42    inference(forward_demodulation,[],[f96,f68])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f67])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_5 | ~spl2_6)),
% 0.21/0.42    inference(forward_demodulation,[],[f91,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0) | (~spl2_1 | ~spl2_6)),
% 0.21/0.42    inference(superposition,[],[f43,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f20])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl2_11 | ~spl2_4 | ~spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f65,f38,f34,f73])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl2_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.42    inference(superposition,[],[f35,f39])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl2_10 | ~spl2_3 | ~spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f38,f30,f67])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl2_3 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_3 | ~spl2_5)),
% 0.21/0.42    inference(superposition,[],[f31,f39])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ~spl2_9 | ~spl2_2 | ~spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f54,f46,f25,f56])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    spl2_2 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl2_7 <=> ! [X1,X0] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ~r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_7)),
% 0.21/0.42    inference(resolution,[],[f47,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    r2_xboole_0(sK0,sK1) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f25])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f46])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f42])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f38])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f34])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f30])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f25])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    r2_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1)) => (k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f20])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (21641)------------------------------
% 0.21/0.42  % (21641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (21641)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (21641)Memory used [KB]: 10618
% 0.21/0.42  % (21641)Time elapsed: 0.007 s
% 0.21/0.42  % (21641)------------------------------
% 0.21/0.42  % (21641)------------------------------
% 0.21/0.43  % (21632)Success in time 0.067 s
%------------------------------------------------------------------------------
