%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:06 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   53 (  71 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   93 ( 129 expanded)
%              Number of equality atoms :   41 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f37,f41,f47,f53,f59,f65,f70])).

fof(f70,plain,
    ( ~ spl2_2
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_2
    | spl2_10 ),
    inference(unit_resulting_resolution,[],[f24,f64])).

fof(f64,plain,
    ( k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_10
  <=> k2_tarski(sK0,sK1) = k1_enumset1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f24,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl2_2
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,
    ( ~ spl2_10
    | ~ spl2_3
    | spl2_9 ),
    inference(avatar_split_clause,[],[f60,f56,f27,f62])).

fof(f27,plain,
    ( spl2_3
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f56,plain,
    ( spl2_9
  <=> k2_tarski(sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f60,plain,
    ( k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)
    | ~ spl2_3
    | spl2_9 ),
    inference(superposition,[],[f58,f28])).

fof(f28,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f58,plain,
    ( k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f56])).

fof(f59,plain,
    ( ~ spl2_9
    | ~ spl2_4
    | spl2_8 ),
    inference(avatar_split_clause,[],[f54,f50,f31,f56])).

fof(f31,plain,
    ( spl2_4
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f50,plain,
    ( spl2_8
  <=> k2_tarski(sK0,sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f54,plain,
    ( k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)
    | ~ spl2_4
    | spl2_8 ),
    inference(superposition,[],[f52,f32])).

fof(f32,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f52,plain,
    ( k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f50])).

fof(f53,plain,
    ( ~ spl2_8
    | ~ spl2_5
    | spl2_7 ),
    inference(avatar_split_clause,[],[f48,f44,f35,f50])).

fof(f35,plain,
    ( spl2_5
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f44,plain,
    ( spl2_7
  <=> k2_tarski(sK0,sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f48,plain,
    ( k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ spl2_5
    | spl2_7 ),
    inference(superposition,[],[f46,f36])).

fof(f36,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f46,plain,
    ( k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f44])).

fof(f47,plain,
    ( ~ spl2_7
    | spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f42,f39,f18,f44])).

fof(f18,plain,
    ( spl2_1
  <=> k2_tarski(sK0,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( spl2_6
  <=> ! [X1,X3,X5,X0,X2,X4] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f42,plain,
    ( k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)
    | spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f20,f40])).

fof(f40,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f20,plain,
    ( k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f41,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(f37,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f33,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.37  ipcrm: permission denied for id (721256449)
% 0.20/0.37  ipcrm: permission denied for id (721289218)
% 0.20/0.37  ipcrm: permission denied for id (722632707)
% 0.20/0.37  ipcrm: permission denied for id (721321989)
% 0.20/0.37  ipcrm: permission denied for id (721354758)
% 0.20/0.37  ipcrm: permission denied for id (721387527)
% 0.20/0.38  ipcrm: permission denied for id (721420297)
% 0.20/0.38  ipcrm: permission denied for id (722796556)
% 0.20/0.39  ipcrm: permission denied for id (722894863)
% 0.20/0.39  ipcrm: permission denied for id (722960401)
% 0.20/0.39  ipcrm: permission denied for id (723025939)
% 0.20/0.39  ipcrm: permission denied for id (723058708)
% 0.20/0.39  ipcrm: permission denied for id (723091477)
% 0.20/0.40  ipcrm: permission denied for id (723157015)
% 0.20/0.40  ipcrm: permission denied for id (723189784)
% 0.20/0.40  ipcrm: permission denied for id (723222553)
% 0.20/0.40  ipcrm: permission denied for id (723386398)
% 0.20/0.41  ipcrm: permission denied for id (721518623)
% 0.20/0.41  ipcrm: permission denied for id (721551392)
% 0.20/0.41  ipcrm: permission denied for id (721584161)
% 0.20/0.41  ipcrm: permission denied for id (721616931)
% 0.20/0.41  ipcrm: permission denied for id (723451940)
% 0.20/0.41  ipcrm: permission denied for id (721682470)
% 0.20/0.42  ipcrm: permission denied for id (723517479)
% 0.20/0.42  ipcrm: permission denied for id (723681323)
% 0.20/0.42  ipcrm: permission denied for id (723714092)
% 0.20/0.42  ipcrm: permission denied for id (723779629)
% 0.20/0.43  ipcrm: permission denied for id (724009012)
% 0.20/0.43  ipcrm: permission denied for id (724041781)
% 0.20/0.44  ipcrm: permission denied for id (721846326)
% 0.20/0.44  ipcrm: permission denied for id (724074551)
% 0.20/0.44  ipcrm: permission denied for id (724172858)
% 0.20/0.44  ipcrm: permission denied for id (724205627)
% 0.20/0.44  ipcrm: permission denied for id (724271165)
% 0.20/0.45  ipcrm: permission denied for id (724467779)
% 0.20/0.45  ipcrm: permission denied for id (724533317)
% 0.20/0.46  ipcrm: permission denied for id (724598855)
% 0.20/0.46  ipcrm: permission denied for id (724664393)
% 0.20/0.46  ipcrm: permission denied for id (724697162)
% 0.20/0.46  ipcrm: permission denied for id (724729931)
% 0.20/0.47  ipcrm: permission denied for id (724795469)
% 0.20/0.47  ipcrm: permission denied for id (724828238)
% 0.20/0.47  ipcrm: permission denied for id (724893776)
% 0.20/0.47  ipcrm: permission denied for id (724992083)
% 0.20/0.48  ipcrm: permission denied for id (725090390)
% 0.20/0.48  ipcrm: permission denied for id (725188697)
% 0.20/0.49  ipcrm: permission denied for id (725319773)
% 0.20/0.49  ipcrm: permission denied for id (725385311)
% 0.20/0.49  ipcrm: permission denied for id (725450849)
% 0.20/0.49  ipcrm: permission denied for id (722141282)
% 0.20/0.49  ipcrm: permission denied for id (722174051)
% 0.20/0.50  ipcrm: permission denied for id (722206821)
% 0.20/0.50  ipcrm: permission denied for id (725516390)
% 0.20/0.50  ipcrm: permission denied for id (725549159)
% 0.20/0.50  ipcrm: permission denied for id (725581928)
% 0.20/0.51  ipcrm: permission denied for id (722272363)
% 0.20/0.51  ipcrm: permission denied for id (722337903)
% 0.20/0.51  ipcrm: permission denied for id (725811312)
% 0.20/0.51  ipcrm: permission denied for id (722370673)
% 0.20/0.52  ipcrm: permission denied for id (725876851)
% 0.20/0.52  ipcrm: permission denied for id (725909620)
% 0.20/0.52  ipcrm: permission denied for id (725942389)
% 0.20/0.52  ipcrm: permission denied for id (726007926)
% 0.20/0.52  ipcrm: permission denied for id (722436215)
% 0.20/0.52  ipcrm: permission denied for id (726073464)
% 0.20/0.52  ipcrm: permission denied for id (726106233)
% 0.20/0.53  ipcrm: permission denied for id (726270078)
% 0.69/0.61  % (23102)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.69/0.62  % (23102)Refutation found. Thanks to Tanya!
% 0.69/0.62  % SZS status Theorem for theBenchmark
% 0.69/0.62  % SZS output start Proof for theBenchmark
% 0.69/0.62  fof(f71,plain,(
% 0.69/0.62    $false),
% 0.69/0.62    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f37,f41,f47,f53,f59,f65,f70])).
% 0.69/0.62  fof(f70,plain,(
% 0.69/0.62    ~spl2_2 | spl2_10),
% 0.69/0.62    inference(avatar_contradiction_clause,[],[f66])).
% 0.69/0.62  fof(f66,plain,(
% 0.69/0.62    $false | (~spl2_2 | spl2_10)),
% 0.69/0.62    inference(unit_resulting_resolution,[],[f24,f64])).
% 0.69/0.62  fof(f64,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) | spl2_10),
% 0.69/0.62    inference(avatar_component_clause,[],[f62])).
% 0.69/0.62  fof(f62,plain,(
% 0.69/0.62    spl2_10 <=> k2_tarski(sK0,sK1) = k1_enumset1(sK0,sK0,sK1)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.69/0.62  fof(f24,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl2_2),
% 0.69/0.62    inference(avatar_component_clause,[],[f23])).
% 0.69/0.62  fof(f23,plain,(
% 0.69/0.62    spl2_2 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.69/0.62  fof(f65,plain,(
% 0.69/0.62    ~spl2_10 | ~spl2_3 | spl2_9),
% 0.69/0.62    inference(avatar_split_clause,[],[f60,f56,f27,f62])).
% 0.69/0.62  fof(f27,plain,(
% 0.69/0.62    spl2_3 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.69/0.62  fof(f56,plain,(
% 0.69/0.62    spl2_9 <=> k2_tarski(sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.69/0.62  fof(f60,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) | (~spl2_3 | spl2_9)),
% 0.69/0.62    inference(superposition,[],[f58,f28])).
% 0.69/0.62  fof(f28,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl2_3),
% 0.69/0.62    inference(avatar_component_clause,[],[f27])).
% 0.69/0.62  fof(f58,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) | spl2_9),
% 0.69/0.62    inference(avatar_component_clause,[],[f56])).
% 0.69/0.62  fof(f59,plain,(
% 0.69/0.62    ~spl2_9 | ~spl2_4 | spl2_8),
% 0.69/0.62    inference(avatar_split_clause,[],[f54,f50,f31,f56])).
% 0.69/0.62  fof(f31,plain,(
% 0.69/0.62    spl2_4 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.69/0.62  fof(f50,plain,(
% 0.69/0.62    spl2_8 <=> k2_tarski(sK0,sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.69/0.62  fof(f54,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) | (~spl2_4 | spl2_8)),
% 0.69/0.62    inference(superposition,[],[f52,f32])).
% 0.69/0.62  fof(f32,plain,(
% 0.69/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) ) | ~spl2_4),
% 0.69/0.62    inference(avatar_component_clause,[],[f31])).
% 0.69/0.62  fof(f52,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) | spl2_8),
% 0.69/0.62    inference(avatar_component_clause,[],[f50])).
% 0.69/0.62  fof(f53,plain,(
% 0.69/0.62    ~spl2_8 | ~spl2_5 | spl2_7),
% 0.69/0.62    inference(avatar_split_clause,[],[f48,f44,f35,f50])).
% 0.69/0.62  fof(f35,plain,(
% 0.69/0.62    spl2_5 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.69/0.62  fof(f44,plain,(
% 0.69/0.62    spl2_7 <=> k2_tarski(sK0,sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.69/0.62  fof(f48,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) | (~spl2_5 | spl2_7)),
% 0.69/0.62    inference(superposition,[],[f46,f36])).
% 0.69/0.62  fof(f36,plain,(
% 0.69/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) ) | ~spl2_5),
% 0.69/0.62    inference(avatar_component_clause,[],[f35])).
% 0.69/0.62  fof(f46,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) | spl2_7),
% 0.69/0.62    inference(avatar_component_clause,[],[f44])).
% 0.69/0.62  fof(f47,plain,(
% 0.69/0.62    ~spl2_7 | spl2_1 | ~spl2_6),
% 0.69/0.62    inference(avatar_split_clause,[],[f42,f39,f18,f44])).
% 0.69/0.62  fof(f18,plain,(
% 0.69/0.62    spl2_1 <=> k2_tarski(sK0,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.69/0.62  fof(f39,plain,(
% 0.69/0.62    spl2_6 <=> ! [X1,X3,X5,X0,X2,X4] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.69/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.69/0.62  fof(f42,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) | (spl2_1 | ~spl2_6)),
% 0.69/0.62    inference(superposition,[],[f20,f40])).
% 0.69/0.62  fof(f40,plain,(
% 0.69/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) ) | ~spl2_6),
% 0.69/0.62    inference(avatar_component_clause,[],[f39])).
% 0.69/0.62  fof(f20,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | spl2_1),
% 0.69/0.62    inference(avatar_component_clause,[],[f18])).
% 0.69/0.62  fof(f41,plain,(
% 0.69/0.62    spl2_6),
% 0.69/0.62    inference(avatar_split_clause,[],[f16,f39])).
% 0.69/0.62  fof(f16,plain,(
% 0.69/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f5])).
% 0.69/0.62  fof(f5,axiom,(
% 0.69/0.62    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).
% 0.69/0.62  fof(f37,plain,(
% 0.69/0.62    spl2_5),
% 0.69/0.62    inference(avatar_split_clause,[],[f15,f35])).
% 0.69/0.62  fof(f15,plain,(
% 0.69/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f4])).
% 0.69/0.62  fof(f4,axiom,(
% 0.69/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.69/0.62  fof(f33,plain,(
% 0.69/0.62    spl2_4),
% 0.69/0.62    inference(avatar_split_clause,[],[f14,f31])).
% 0.69/0.62  fof(f14,plain,(
% 0.69/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f3])).
% 0.69/0.62  fof(f3,axiom,(
% 0.69/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.69/0.62  fof(f29,plain,(
% 0.69/0.62    spl2_3),
% 0.69/0.62    inference(avatar_split_clause,[],[f13,f27])).
% 0.69/0.62  fof(f13,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f2])).
% 0.69/0.62  fof(f2,axiom,(
% 0.69/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.69/0.62  fof(f25,plain,(
% 0.69/0.62    spl2_2),
% 0.69/0.62    inference(avatar_split_clause,[],[f12,f23])).
% 0.69/0.62  fof(f12,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f1])).
% 0.69/0.62  fof(f1,axiom,(
% 0.69/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.69/0.62  fof(f21,plain,(
% 0.69/0.62    ~spl2_1),
% 0.69/0.62    inference(avatar_split_clause,[],[f11,f18])).
% 0.69/0.62  fof(f11,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.69/0.62    inference(cnf_transformation,[],[f10])).
% 0.69/0.62  fof(f10,plain,(
% 0.69/0.62    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.69/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 0.69/0.62  fof(f9,plain,(
% 0.69/0.62    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.69/0.62    introduced(choice_axiom,[])).
% 0.69/0.62  fof(f8,plain,(
% 0.69/0.62    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.69/0.62    inference(ennf_transformation,[],[f7])).
% 0.69/0.62  fof(f7,negated_conjecture,(
% 0.69/0.62    ~! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.69/0.62    inference(negated_conjecture,[],[f6])).
% 0.69/0.62  fof(f6,conjecture,(
% 0.69/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).
% 0.69/0.62  % SZS output end Proof for theBenchmark
% 0.69/0.62  % (23102)------------------------------
% 0.69/0.62  % (23102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.69/0.62  % (23102)Termination reason: Refutation
% 0.69/0.62  
% 0.69/0.62  % (23102)Memory used [KB]: 6140
% 0.69/0.62  % (23102)Time elapsed: 0.026 s
% 0.69/0.62  % (23102)------------------------------
% 0.69/0.62  % (23102)------------------------------
% 0.69/0.62  % (22871)Success in time 0.259 s
%------------------------------------------------------------------------------
