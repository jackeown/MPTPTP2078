%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 105 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f46,f64,f72,f90,f138,f149])).

fof(f149,plain,
    ( spl6_1
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl6_1
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f29,f139])).

fof(f139,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f89,f137])).

fof(f137,plain,
    ( ! [X12,X10,X8,X7,X13,X11,X9] :
        ( k4_enumset1(X8,X9,X10,X11,X12,X13) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13)
        | ~ r1_tarski(k1_tarski(X7),k4_enumset1(X8,X9,X10,X11,X12,X13)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_18
  <=> ! [X9,X11,X13,X7,X8,X10,X12] :
        ( k4_enumset1(X8,X9,X10,X11,X12,X13) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13)
        | ~ r1_tarski(k1_tarski(X7),k4_enumset1(X8,X9,X10,X11,X12,X13)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f89,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : r1_tarski(k1_tarski(X6),k4_enumset1(X6,X7,X8,X9,X10,X11))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_12
  <=> ! [X9,X11,X7,X8,X10,X6] : r1_tarski(k1_tarski(X6),k4_enumset1(X6,X7,X8,X9,X10,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f29,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl6_1
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f138,plain,
    ( spl6_18
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f78,f70,f44,f136])).

fof(f44,plain,
    ( spl6_5
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f70,plain,
    ( spl6_10
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f78,plain,
    ( ! [X12,X10,X8,X7,X13,X11,X9] :
        ( k4_enumset1(X8,X9,X10,X11,X12,X13) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13)
        | ~ r1_tarski(k1_tarski(X7),k4_enumset1(X8,X9,X10,X11,X12,X13)) )
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(superposition,[],[f71,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f71,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f90,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f68,f62,f32,f88])).

fof(f32,plain,
    ( spl6_2
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f62,plain,
    ( spl6_9
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f68,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : r1_tarski(k1_tarski(X6),k4_enumset1(X6,X7,X8,X9,X10,X11))
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(superposition,[],[f33,f63])).

fof(f63,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f33,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f72,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f64,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f46,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f34,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f30,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (30430)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.43  % (30430)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f154,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f30,f34,f46,f64,f72,f90,f138,f149])).
% 0.21/0.43  fof(f149,plain,(
% 0.21/0.43    spl6_1 | ~spl6_12 | ~spl6_18),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.43  fof(f148,plain,(
% 0.21/0.43    $false | (spl6_1 | ~spl6_12 | ~spl6_18)),
% 0.21/0.43    inference(subsumption_resolution,[],[f29,f139])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ) | (~spl6_12 | ~spl6_18)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f89,f137])).
% 0.21/0.43  fof(f137,plain,(
% 0.21/0.43    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k4_enumset1(X8,X9,X10,X11,X12,X13) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13) | ~r1_tarski(k1_tarski(X7),k4_enumset1(X8,X9,X10,X11,X12,X13))) ) | ~spl6_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f136])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    spl6_18 <=> ! [X9,X11,X13,X7,X8,X10,X12] : (k4_enumset1(X8,X9,X10,X11,X12,X13) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13) | ~r1_tarski(k1_tarski(X7),k4_enumset1(X8,X9,X10,X11,X12,X13)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    ( ! [X6,X10,X8,X7,X11,X9] : (r1_tarski(k1_tarski(X6),k4_enumset1(X6,X7,X8,X9,X10,X11))) ) | ~spl6_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f88])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    spl6_12 <=> ! [X9,X11,X7,X8,X10,X6] : r1_tarski(k1_tarski(X6),k4_enumset1(X6,X7,X8,X9,X10,X11))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) | spl6_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    spl6_1 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    spl6_18 | ~spl6_5 | ~spl6_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f78,f70,f44,f136])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl6_5 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl6_10 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k4_enumset1(X8,X9,X10,X11,X12,X13) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13) | ~r1_tarski(k1_tarski(X7),k4_enumset1(X8,X9,X10,X11,X12,X13))) ) | (~spl6_5 | ~spl6_10)),
% 0.21/0.43    inference(superposition,[],[f71,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl6_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) ) | ~spl6_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f70])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    spl6_12 | ~spl6_2 | ~spl6_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f68,f62,f32,f88])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl6_2 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl6_9 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X6,X10,X8,X7,X11,X9] : (r1_tarski(k1_tarski(X6),k4_enumset1(X6,X7,X8,X9,X10,X11))) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.43    inference(superposition,[],[f33,f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl6_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl6_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    spl6_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f70])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl6_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f62])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl6_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f44])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl6_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f32])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ~spl6_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f27])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.43    inference(negated_conjecture,[],[f10])).
% 0.21/0.43  fof(f10,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (30430)------------------------------
% 0.21/0.43  % (30430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (30430)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (30430)Memory used [KB]: 6140
% 0.21/0.43  % (30430)Time elapsed: 0.008 s
% 0.21/0.43  % (30430)------------------------------
% 0.21/0.43  % (30430)------------------------------
% 0.21/0.43  % (30424)Success in time 0.078 s
%------------------------------------------------------------------------------
