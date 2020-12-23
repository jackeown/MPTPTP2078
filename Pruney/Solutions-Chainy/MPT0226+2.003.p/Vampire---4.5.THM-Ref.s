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
% DateTime   : Thu Dec  3 12:36:13 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   48 (  84 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 124 expanded)
%              Number of equality atoms :   52 (  95 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f166,f174,f211])).

fof(f211,plain,
    ( spl2_1
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f63,f172,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X0) != k1_enumset1(X1,X1,X2)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f28,f47,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f172,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl2_6
  <=> k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f63,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f174,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f168,f163,f170])).

fof(f163,plain,
    ( spl2_5
  <=> k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f168,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f40,f165])).

fof(f165,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f163])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f166,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f161,f66,f163])).

fof(f66,plain,
    ( spl2_2
  <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f161,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f150,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f44,f44])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f150,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK1,sK1,sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f50,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X2),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f37,f46,f44,f47])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f69,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f51,f66])).

fof(f51,plain,(
    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f26,f33,f47,f47])).

fof(f26,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f64,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:29:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.35/0.56  % (1469)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.56  % (1489)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.35/0.56  % (1480)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.57  % (1472)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.65/0.57  % (1494)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.65/0.58  % (1489)Refutation found. Thanks to Tanya!
% 1.65/0.58  % SZS status Theorem for theBenchmark
% 1.65/0.58  % (1477)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.65/0.58  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f215,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(avatar_sat_refutation,[],[f64,f69,f166,f174,f211])).
% 1.65/0.58  fof(f211,plain,(
% 1.65/0.58    spl2_1 | ~spl2_6),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f195])).
% 1.65/0.58  fof(f195,plain,(
% 1.65/0.58    $false | (spl2_1 | ~spl2_6)),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f63,f172,f52])).
% 1.65/0.58  fof(f52,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X0) != k1_enumset1(X1,X1,X2) | X0 = X1) )),
% 1.65/0.58    inference(definition_unfolding,[],[f28,f47,f44])).
% 1.65/0.58  fof(f44,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,axiom,(
% 1.65/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.65/0.58  fof(f47,plain,(
% 1.65/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f31,f44])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f14])).
% 1.65/0.58  fof(f14,axiom,(
% 1.65/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (X0 = X1 | k1_tarski(X0) != k2_tarski(X1,X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f23])).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (X0 = X1 | k1_tarski(X0) != k2_tarski(X1,X2))),
% 1.65/0.58    inference(ennf_transformation,[],[f19])).
% 1.65/0.58  fof(f19,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 1.65/0.58  fof(f172,plain,(
% 1.65/0.58    k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1) | ~spl2_6),
% 1.65/0.58    inference(avatar_component_clause,[],[f170])).
% 1.65/0.58  fof(f170,plain,(
% 1.65/0.58    spl2_6 <=> k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.65/0.58  fof(f63,plain,(
% 1.65/0.58    sK0 != sK1 | spl2_1),
% 1.65/0.58    inference(avatar_component_clause,[],[f61])).
% 1.65/0.58  fof(f61,plain,(
% 1.65/0.58    spl2_1 <=> sK0 = sK1),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.65/0.58  fof(f174,plain,(
% 1.65/0.58    spl2_6 | ~spl2_5),
% 1.65/0.58    inference(avatar_split_clause,[],[f168,f163,f170])).
% 1.65/0.58  fof(f163,plain,(
% 1.65/0.58    spl2_5 <=> k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.65/0.58  fof(f168,plain,(
% 1.65/0.58    k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1) | ~spl2_5),
% 1.65/0.58    inference(superposition,[],[f40,f165])).
% 1.65/0.58  fof(f165,plain,(
% 1.65/0.58    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1) | ~spl2_5),
% 1.65/0.58    inference(avatar_component_clause,[],[f163])).
% 1.65/0.58  fof(f40,plain,(
% 1.65/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.65/0.58    inference(cnf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,axiom,(
% 1.65/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.65/0.58  fof(f166,plain,(
% 1.65/0.58    spl2_5 | ~spl2_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f161,f66,f163])).
% 1.65/0.58  fof(f66,plain,(
% 1.65/0.58    spl2_2 <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.65/0.58  fof(f161,plain,(
% 1.65/0.58    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1) | ~spl2_2),
% 1.65/0.58    inference(forward_demodulation,[],[f150,f53])).
% 1.65/0.58  fof(f53,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f29,f44,f44])).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f8])).
% 1.65/0.58  fof(f8,axiom,(
% 1.65/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.65/0.58  fof(f150,plain,(
% 1.65/0.58    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK1,sK1,sK0) | ~spl2_2),
% 1.65/0.58    inference(superposition,[],[f50,f68])).
% 1.65/0.58  fof(f68,plain,(
% 1.65/0.58    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) | ~spl2_2),
% 1.65/0.58    inference(avatar_component_clause,[],[f66])).
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X2),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f37,f46,f44,f47])).
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f32,f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.65/0.59  fof(f32,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f7])).
% 1.65/0.59  fof(f7,axiom,(
% 1.65/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.65/0.59  fof(f37,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f11])).
% 1.65/0.59  fof(f11,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 1.65/0.59  fof(f69,plain,(
% 1.65/0.59    spl2_2),
% 1.65/0.59    inference(avatar_split_clause,[],[f51,f66])).
% 1.65/0.59  fof(f51,plain,(
% 1.65/0.59    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))),
% 1.65/0.59    inference(definition_unfolding,[],[f26,f33,f47,f47])).
% 1.65/0.59  fof(f26,plain,(
% 1.65/0.59    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.65/0.59    inference(cnf_transformation,[],[f25])).
% 1.65/0.59  fof(f25,plain,(
% 1.65/0.59    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.65/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).
% 1.65/0.59  fof(f24,plain,(
% 1.65/0.59    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f22,plain,(
% 1.65/0.59    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.65/0.59    inference(ennf_transformation,[],[f21])).
% 1.65/0.59  fof(f21,negated_conjecture,(
% 1.65/0.59    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.65/0.59    inference(negated_conjecture,[],[f20])).
% 1.65/0.59  fof(f20,conjecture,(
% 1.65/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.65/0.59  fof(f64,plain,(
% 1.65/0.59    ~spl2_1),
% 1.65/0.59    inference(avatar_split_clause,[],[f27,f61])).
% 1.65/0.59  fof(f27,plain,(
% 1.65/0.59    sK0 != sK1),
% 1.65/0.59    inference(cnf_transformation,[],[f25])).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (1489)------------------------------
% 1.65/0.59  % (1489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (1489)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (1489)Memory used [KB]: 10746
% 1.65/0.59  % (1489)Time elapsed: 0.091 s
% 1.65/0.59  % (1489)------------------------------
% 1.65/0.59  % (1489)------------------------------
% 1.65/0.59  % (1464)Success in time 0.227 s
%------------------------------------------------------------------------------
