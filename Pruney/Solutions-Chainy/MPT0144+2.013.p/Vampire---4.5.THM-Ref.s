%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  83 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f45,f53,f76,f81,f213,f224])).

fof(f224,plain,
    ( spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl7_1
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f28,f222])).

fof(f222,plain,
    ( ! [X37,X35,X33,X38,X36,X34,X32] : k2_xboole_0(k3_enumset1(X35,X36,X37,X38,X32),k2_tarski(X33,X34)) = k5_enumset1(X35,X36,X37,X38,X32,X33,X34)
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f218,f80])).

fof(f80,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_10
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f218,plain,
    ( ! [X37,X35,X33,X38,X36,X34,X32] : k2_xboole_0(k3_enumset1(X35,X36,X37,X38,X32),k2_tarski(X33,X34)) = k2_xboole_0(k2_enumset1(X35,X36,X37,X38),k1_enumset1(X32,X33,X34))
    | ~ spl7_5
    | ~ spl7_19 ),
    inference(superposition,[],[f212,f44])).

fof(f44,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl7_5
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f212,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl7_19
  <=> ! [X1,X3,X5,X0,X2,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f28,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f213,plain,
    ( spl7_19
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f77,f74,f51,f211])).

fof(f51,plain,
    ( spl7_7
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f74,plain,
    ( spl7_9
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f77,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(superposition,[],[f52,f75])).

fof(f75,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f52,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f81,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f24,f79])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f76,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f23,f74])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f53,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f45,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f29,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:10:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (24454)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.43  % (24454)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f227,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f29,f45,f53,f76,f81,f213,f224])).
% 0.19/0.43  fof(f224,plain,(
% 0.19/0.43    spl7_1 | ~spl7_5 | ~spl7_10 | ~spl7_19),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f223])).
% 0.19/0.43  fof(f223,plain,(
% 0.19/0.43    $false | (spl7_1 | ~spl7_5 | ~spl7_10 | ~spl7_19)),
% 0.19/0.43    inference(subsumption_resolution,[],[f28,f222])).
% 0.19/0.43  fof(f222,plain,(
% 0.19/0.43    ( ! [X37,X35,X33,X38,X36,X34,X32] : (k2_xboole_0(k3_enumset1(X35,X36,X37,X38,X32),k2_tarski(X33,X34)) = k5_enumset1(X35,X36,X37,X38,X32,X33,X34)) ) | (~spl7_5 | ~spl7_10 | ~spl7_19)),
% 0.19/0.43    inference(forward_demodulation,[],[f218,f80])).
% 0.19/0.43  fof(f80,plain,(
% 0.19/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) ) | ~spl7_10),
% 0.19/0.43    inference(avatar_component_clause,[],[f79])).
% 0.19/0.43  fof(f79,plain,(
% 0.19/0.43    spl7_10 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.19/0.43  fof(f218,plain,(
% 0.19/0.43    ( ! [X37,X35,X33,X38,X36,X34,X32] : (k2_xboole_0(k3_enumset1(X35,X36,X37,X38,X32),k2_tarski(X33,X34)) = k2_xboole_0(k2_enumset1(X35,X36,X37,X38),k1_enumset1(X32,X33,X34))) ) | (~spl7_5 | ~spl7_19)),
% 0.19/0.43    inference(superposition,[],[f212,f44])).
% 0.19/0.43  fof(f44,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl7_5),
% 0.19/0.43    inference(avatar_component_clause,[],[f43])).
% 0.19/0.43  fof(f43,plain,(
% 0.19/0.43    spl7_5 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.19/0.43  fof(f212,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)) ) | ~spl7_19),
% 0.19/0.43    inference(avatar_component_clause,[],[f211])).
% 0.19/0.43  fof(f211,plain,(
% 0.19/0.43    spl7_19 <=> ! [X1,X3,X5,X0,X2,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) | spl7_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f26])).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    spl7_1 <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.19/0.43  fof(f213,plain,(
% 0.19/0.43    spl7_19 | ~spl7_7 | ~spl7_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f77,f74,f51,f211])).
% 0.19/0.43  fof(f51,plain,(
% 0.19/0.43    spl7_7 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.19/0.43  fof(f74,plain,(
% 0.19/0.43    spl7_9 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.19/0.43  fof(f77,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)) ) | (~spl7_7 | ~spl7_9)),
% 0.19/0.43    inference(superposition,[],[f52,f75])).
% 0.19/0.43  fof(f75,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | ~spl7_9),
% 0.19/0.43    inference(avatar_component_clause,[],[f74])).
% 0.19/0.43  fof(f52,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl7_7),
% 0.19/0.43    inference(avatar_component_clause,[],[f51])).
% 0.19/0.43  fof(f81,plain,(
% 0.19/0.43    spl7_10),
% 0.19/0.43    inference(avatar_split_clause,[],[f24,f79])).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 0.19/0.43  fof(f76,plain,(
% 0.19/0.43    spl7_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f23,f74])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.19/0.43  fof(f53,plain,(
% 0.19/0.43    spl7_7),
% 0.19/0.43    inference(avatar_split_clause,[],[f21,f51])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.19/0.43  fof(f45,plain,(
% 0.19/0.43    spl7_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f19,f43])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f7])).
% 0.19/0.43  fof(f7,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    ~spl7_1),
% 0.19/0.43    inference(avatar_split_clause,[],[f15,f26])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.19/0.43    inference(cnf_transformation,[],[f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.19/0.43    inference(ennf_transformation,[],[f11])).
% 0.19/0.44  fof(f11,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.19/0.44    inference(negated_conjecture,[],[f10])).
% 0.19/0.44  fof(f10,conjecture,(
% 0.19/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (24454)------------------------------
% 0.19/0.44  % (24454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (24454)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (24454)Memory used [KB]: 6268
% 0.19/0.44  % (24454)Time elapsed: 0.058 s
% 0.19/0.44  % (24454)------------------------------
% 0.19/0.44  % (24454)------------------------------
% 0.19/0.44  % (24448)Success in time 0.097 s
%------------------------------------------------------------------------------
