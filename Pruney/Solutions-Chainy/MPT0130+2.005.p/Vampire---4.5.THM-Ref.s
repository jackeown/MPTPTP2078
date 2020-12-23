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
% DateTime   : Thu Dec  3 12:33:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  74 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 155 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f56,f74,f86,f127,f599,f826,f2608,f2642])).

fof(f2642,plain,
    ( spl4_2
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_36
    | ~ spl4_67 ),
    inference(avatar_contradiction_clause,[],[f2641])).

fof(f2641,plain,
    ( $false
    | spl4_2
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_36
    | ~ spl4_67 ),
    inference(subsumption_resolution,[],[f43,f2640])).

fof(f2640,plain,
    ( ! [X12,X10,X13,X11] : k2_xboole_0(k1_enumset1(X13,X10,X11),k1_tarski(X12)) = k2_enumset1(X13,X10,X11,X12)
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_36
    | ~ spl4_67 ),
    inference(forward_demodulation,[],[f2614,f622])).

fof(f622,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X6),k1_enumset1(X3,X4,X5)) = k2_enumset1(X6,X3,X4,X5)
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f601,f126])).

fof(f126,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_14
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f601,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k2_tarski(X6,X3),k2_tarski(X4,X5)) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X3,X4,X5))
    | ~ spl4_8
    | ~ spl4_31 ),
    inference(superposition,[],[f598,f73])).

fof(f73,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f598,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl4_31
  <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f2614,plain,
    ( ! [X12,X10,X13,X11] : k2_xboole_0(k1_enumset1(X13,X10,X11),k1_tarski(X12)) = k2_xboole_0(k1_tarski(X13),k1_enumset1(X10,X11,X12))
    | ~ spl4_36
    | ~ spl4_67 ),
    inference(superposition,[],[f825,f2607])).

fof(f2607,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1))
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f2606])).

fof(f2606,plain,
    ( spl4_67
  <=> ! [X1,X0,X2] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f825,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl4_36
  <=> ! [X3,X5,X4,X6] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f43,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2608,plain,
    ( spl4_67
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f621,f597,f72,f54,f2606])).

fof(f54,plain,
    ( spl4_5
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f621,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1))
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f600,f73])).

fof(f600,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))
    | ~ spl4_5
    | ~ spl4_31 ),
    inference(superposition,[],[f598,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f826,plain,
    ( spl4_36
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f114,f84,f72,f824])).

fof(f84,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f114,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(superposition,[],[f85,f73])).

fof(f85,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f599,plain,
    ( spl4_31
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f113,f84,f54,f597])).

fof(f113,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(superposition,[],[f85,f55])).

fof(f127,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f31,f125])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(f86,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f29,f84])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f74,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f72])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f56,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f44,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:43:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (20595)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (20603)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (20595)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f2648,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f44,f56,f74,f86,f127,f599,f826,f2608,f2642])).
% 0.22/0.49  fof(f2642,plain,(
% 0.22/0.49    spl4_2 | ~spl4_8 | ~spl4_14 | ~spl4_31 | ~spl4_36 | ~spl4_67),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f2641])).
% 0.22/0.49  fof(f2641,plain,(
% 0.22/0.49    $false | (spl4_2 | ~spl4_8 | ~spl4_14 | ~spl4_31 | ~spl4_36 | ~spl4_67)),
% 0.22/0.49    inference(subsumption_resolution,[],[f43,f2640])).
% 0.22/0.49  fof(f2640,plain,(
% 0.22/0.49    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k1_enumset1(X13,X10,X11),k1_tarski(X12)) = k2_enumset1(X13,X10,X11,X12)) ) | (~spl4_8 | ~spl4_14 | ~spl4_31 | ~spl4_36 | ~spl4_67)),
% 0.22/0.49    inference(forward_demodulation,[],[f2614,f622])).
% 0.22/0.49  fof(f622,plain,(
% 0.22/0.49    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X6),k1_enumset1(X3,X4,X5)) = k2_enumset1(X6,X3,X4,X5)) ) | (~spl4_8 | ~spl4_14 | ~spl4_31)),
% 0.22/0.49    inference(forward_demodulation,[],[f601,f126])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl4_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f125])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    spl4_14 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.49  fof(f601,plain,(
% 0.22/0.49    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k2_tarski(X6,X3),k2_tarski(X4,X5)) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X3,X4,X5))) ) | (~spl4_8 | ~spl4_31)),
% 0.22/0.49    inference(superposition,[],[f598,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl4_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl4_8 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.49  fof(f598,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | ~spl4_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f597])).
% 0.22/0.49  fof(f597,plain,(
% 0.22/0.49    spl4_31 <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.49  fof(f2614,plain,(
% 0.22/0.49    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k1_enumset1(X13,X10,X11),k1_tarski(X12)) = k2_xboole_0(k1_tarski(X13),k1_enumset1(X10,X11,X12))) ) | (~spl4_36 | ~spl4_67)),
% 0.22/0.49    inference(superposition,[],[f825,f2607])).
% 0.22/0.49  fof(f2607,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1))) ) | ~spl4_67),
% 0.22/0.49    inference(avatar_component_clause,[],[f2606])).
% 0.22/0.49  fof(f2606,plain,(
% 0.22/0.49    spl4_67 <=> ! [X1,X0,X2] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.22/0.49  fof(f825,plain,(
% 0.22/0.49    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ) | ~spl4_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f824])).
% 0.22/0.49  fof(f824,plain,(
% 0.22/0.49    spl4_36 <=> ! [X3,X5,X4,X6] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) | spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    spl4_2 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f2608,plain,(
% 0.22/0.49    spl4_67 | ~spl4_5 | ~spl4_8 | ~spl4_31),
% 0.22/0.49    inference(avatar_split_clause,[],[f621,f597,f72,f54,f2606])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl4_5 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.49  fof(f621,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1))) ) | (~spl4_5 | ~spl4_8 | ~spl4_31)),
% 0.22/0.49    inference(forward_demodulation,[],[f600,f73])).
% 0.22/0.49  fof(f600,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) ) | (~spl4_5 | ~spl4_31)),
% 0.22/0.49    inference(superposition,[],[f598,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f54])).
% 0.22/0.49  fof(f826,plain,(
% 0.22/0.49    spl4_36 | ~spl4_8 | ~spl4_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f114,f84,f72,f824])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl4_11 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ) | (~spl4_8 | ~spl4_11)),
% 0.22/0.49    inference(superposition,[],[f85,f73])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f84])).
% 0.22/0.49  fof(f599,plain,(
% 0.22/0.49    spl4_31 | ~spl4_5 | ~spl4_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f113,f84,f54,f597])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | (~spl4_5 | ~spl4_11)),
% 0.22/0.49    inference(superposition,[],[f85,f55])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    spl4_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f125])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl4_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f84])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f72])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f54])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ~spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f19,f41])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.49    inference(negated_conjecture,[],[f14])).
% 0.22/0.49  fof(f14,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (20595)------------------------------
% 0.22/0.49  % (20595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20595)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (20595)Memory used [KB]: 8443
% 0.22/0.49  % (20595)Time elapsed: 0.070 s
% 0.22/0.49  % (20595)------------------------------
% 0.22/0.49  % (20595)------------------------------
% 0.22/0.50  % (20587)Success in time 0.13 s
%------------------------------------------------------------------------------
