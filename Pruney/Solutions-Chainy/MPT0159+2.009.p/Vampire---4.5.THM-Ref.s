%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 105 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f48,f70,f82,f96,f144,f155])).

fof(f155,plain,
    ( spl7_1
    | ~ spl7_13
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl7_1
    | ~ spl7_13
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f31,f145])).

fof(f145,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
    | ~ spl7_13
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f95,f143])).

fof(f143,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] :
        ( k5_enumset1(X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)
        | ~ r1_tarski(k1_tarski(X8),k5_enumset1(X9,X10,X11,X12,X13,X14,X15)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_19
  <=> ! [X9,X11,X13,X15,X8,X10,X12,X14] :
        ( k5_enumset1(X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)
        | ~ r1_tarski(k1_tarski(X8),k5_enumset1(X9,X10,X11,X12,X13,X14,X15)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f95,plain,
    ( ! [X12,X10,X8,X7,X13,X11,X9] : r1_tarski(k1_tarski(X7),k5_enumset1(X7,X8,X9,X10,X11,X12,X13))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_13
  <=> ! [X9,X11,X13,X7,X8,X10,X12] : r1_tarski(k1_tarski(X7),k5_enumset1(X7,X8,X9,X10,X11,X12,X13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f31,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f144,plain,
    ( spl7_19
    | ~ spl7_5
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f84,f80,f46,f142])).

fof(f46,plain,
    ( spl7_5
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f80,plain,
    ( spl7_12
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f84,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] :
        ( k5_enumset1(X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)
        | ~ r1_tarski(k1_tarski(X8),k5_enumset1(X9,X10,X11,X12,X13,X14,X15)) )
    | ~ spl7_5
    | ~ spl7_12 ),
    inference(superposition,[],[f81,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f81,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f96,plain,
    ( spl7_13
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f78,f68,f34,f94])).

fof(f34,plain,
    ( spl7_2
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f68,plain,
    ( spl7_10
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f78,plain,
    ( ! [X12,X10,X8,X7,X13,X11,X9] : r1_tarski(k1_tarski(X7),k5_enumset1(X7,X8,X9,X10,X11,X12,X13))
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(superposition,[],[f35,f69])).

fof(f69,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f35,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f82,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f27,f80])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f70,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f48,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f36,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f32,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f16])).

% (24501)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f16,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (24504)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (24504)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (24503)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (24509)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (24505)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (24510)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (24502)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (24510)Refutation not found, incomplete strategy% (24510)------------------------------
% 0.22/0.50  % (24510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24513)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (24510)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (24510)Memory used [KB]: 10618
% 0.22/0.50  % (24510)Time elapsed: 0.068 s
% 0.22/0.50  % (24510)------------------------------
% 0.22/0.50  % (24510)------------------------------
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f32,f36,f48,f70,f82,f96,f144,f155])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl7_1 | ~spl7_13 | ~spl7_19),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    $false | (spl7_1 | ~spl7_13 | ~spl7_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f31,f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ) | (~spl7_13 | ~spl7_19)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f95,f143])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k5_enumset1(X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) | ~r1_tarski(k1_tarski(X8),k5_enumset1(X9,X10,X11,X12,X13,X14,X15))) ) | ~spl7_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl7_19 <=> ! [X9,X11,X13,X15,X8,X10,X12,X14] : (k5_enumset1(X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) | ~r1_tarski(k1_tarski(X8),k5_enumset1(X9,X10,X11,X12,X13,X14,X15)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X12,X10,X8,X7,X13,X11,X9] : (r1_tarski(k1_tarski(X7),k5_enumset1(X7,X8,X9,X10,X11,X12,X13))) ) | ~spl7_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl7_13 <=> ! [X9,X11,X13,X7,X8,X10,X12] : r1_tarski(k1_tarski(X7),k5_enumset1(X7,X8,X9,X10,X11,X12,X13))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) | spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    spl7_1 <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl7_19 | ~spl7_5 | ~spl7_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f84,f80,f46,f142])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl7_5 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl7_12 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k5_enumset1(X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) | ~r1_tarski(k1_tarski(X8),k5_enumset1(X9,X10,X11,X12,X13,X14,X15))) ) | (~spl7_5 | ~spl7_12)),
% 0.22/0.50    inference(superposition,[],[f81,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl7_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f46])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) ) | ~spl7_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl7_13 | ~spl7_2 | ~spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f78,f68,f34,f94])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    spl7_2 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl7_10 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X12,X10,X8,X7,X13,X11,X9] : (r1_tarski(k1_tarski(X7),k5_enumset1(X7,X8,X9,X10,X11,X12,X13))) ) | (~spl7_2 | ~spl7_10)),
% 0.22/0.50    inference(superposition,[],[f35,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) ) | ~spl7_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f34])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl7_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f80])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f68])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f46])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f19,f34])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ~spl7_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f17,f29])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  % (24501)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24504)------------------------------
% 0.22/0.50  % (24504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24504)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24504)Memory used [KB]: 6140
% 0.22/0.50  % (24504)Time elapsed: 0.059 s
% 0.22/0.50  % (24504)------------------------------
% 0.22/0.50  % (24504)------------------------------
% 0.22/0.50  % (24500)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (24498)Success in time 0.138 s
%------------------------------------------------------------------------------
