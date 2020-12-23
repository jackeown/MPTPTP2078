%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  83 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f23,f27,f31,f40,f45,f53])).

fof(f53,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f18,f51])).

fof(f51,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X6),k1_enumset1(X3,X4,X5)) = k2_enumset1(X6,X3,X4,X5)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f47,f39])).

fof(f39,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_5
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f47,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k2_tarski(X6,X3),k2_tarski(X4,X5)) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X3,X4,X5))
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(superposition,[],[f44,f26])).

fof(f26,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl4_3
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f44,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f18,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f45,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f32,f29,f21,f43])).

fof(f21,plain,
    ( spl4_2
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f29,plain,
    ( spl4_4
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f32,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f30,f22])).

fof(f22,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f30,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f40,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f14,f38])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f31,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f27,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f23,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f11,f21])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f19,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f10,f16])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (27918)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (27913)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (27913)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f19,f23,f27,f31,f40,f45,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    $false | (spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f18,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X6),k1_enumset1(X3,X4,X5)) = k2_enumset1(X6,X3,X4,X5)) ) | (~spl4_3 | ~spl4_5 | ~spl4_6)),
% 0.22/0.49    inference(forward_demodulation,[],[f47,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl4_5 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k2_tarski(X6,X3),k2_tarski(X4,X5)) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X3,X4,X5))) ) | (~spl4_3 | ~spl4_6)),
% 0.22/0.49    inference(superposition,[],[f44,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    spl4_3 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | ~spl4_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    spl4_6 <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) | spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    spl4_6 | ~spl4_2 | ~spl4_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f29,f21,f43])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    spl4_2 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    spl4_4 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | (~spl4_2 | ~spl4_4)),
% 0.22/0.49    inference(superposition,[],[f30,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f21])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f29])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f14,f38])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    spl4_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f13,f29])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    spl4_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f12,f25])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f11,f21])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ~spl4_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f10,f16])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (27913)------------------------------
% 0.22/0.49  % (27913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27913)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (27913)Memory used [KB]: 6140
% 0.22/0.49  % (27913)Time elapsed: 0.064 s
% 0.22/0.49  % (27913)------------------------------
% 0.22/0.49  % (27913)------------------------------
% 0.22/0.49  % (27911)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (27907)Success in time 0.128 s
%------------------------------------------------------------------------------
