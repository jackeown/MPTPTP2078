%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 108 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  133 ( 211 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f751,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f84,f108,f133,f340,f700,f730,f750])).

fof(f750,plain,(
    spl3_29 ),
    inference(avatar_contradiction_clause,[],[f746])).

fof(f746,plain,
    ( $false
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f22,f729])).

fof(f729,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl3_29
  <=> k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f730,plain,
    ( ~ spl3_29
    | spl3_8
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f712,f697,f129,f727])).

fof(f129,plain,
    ( spl3_8
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f697,plain,
    ( spl3_28
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f712,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | spl3_8
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f131,f699])).

fof(f699,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f697])).

fof(f131,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f700,plain,
    ( spl3_28
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f695,f80,f697])).

fof(f80,plain,
    ( spl3_5
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f695,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f657,f82])).

fof(f82,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f657,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f139,f76])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f35,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f139,plain,
    ( ! [X14] : k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X14)) = k3_xboole_0(sK0,X14)
    | ~ spl3_5 ),
    inference(superposition,[],[f32,f82])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f340,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f339,f80,f104])).

fof(f104,plain,
    ( spl3_7
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f339,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f329,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f329,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f139,f85])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(unit_resulting_resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f133,plain,
    ( ~ spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f125,f39,f129])).

fof(f39,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f125,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(resolution,[],[f37,f41])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f108,plain,
    ( ~ spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f101,f43,f104])).

fof(f43,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f101,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f77,f48,f80])).

fof(f48,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f77,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f27,f50])).

fof(f50,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f48])).

fof(f33,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f19,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f46,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f43,f39])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (21142)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (21138)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (21146)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (21140)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (21139)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (21148)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (21136)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (21145)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (21150)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (21149)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (21133)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (21141)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (21135)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (21139)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f751,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f46,f51,f84,f108,f133,f340,f700,f730,f750])).
% 0.21/0.52  fof(f750,plain,(
% 0.21/0.52    spl3_29),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f746])).
% 0.21/0.52  fof(f746,plain,(
% 0.21/0.52    $false | spl3_29),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f22,f729])).
% 0.21/0.52  fof(f729,plain,(
% 0.21/0.52    k1_xboole_0 != k5_xboole_0(sK0,sK0) | spl3_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f727])).
% 0.21/0.52  fof(f727,plain,(
% 0.21/0.52    spl3_29 <=> k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.52  fof(f730,plain,(
% 0.21/0.52    ~spl3_29 | spl3_8 | ~spl3_28),
% 0.21/0.52    inference(avatar_split_clause,[],[f712,f697,f129,f727])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl3_8 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f697,plain,(
% 0.21/0.52    spl3_28 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.52  fof(f712,plain,(
% 0.21/0.52    k1_xboole_0 != k5_xboole_0(sK0,sK0) | (spl3_8 | ~spl3_28)),
% 0.21/0.52    inference(backward_demodulation,[],[f131,f699])).
% 0.21/0.52  fof(f699,plain,(
% 0.21/0.52    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f697])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f700,plain,(
% 0.21/0.52    spl3_28 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f695,f80,f697])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl3_5 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f695,plain,(
% 0.21/0.52    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_5),
% 0.21/0.52    inference(forward_demodulation,[],[f657,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f657,plain,(
% 0.21/0.52    k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1) | ~spl3_5),
% 0.21/0.52    inference(superposition,[],[f139,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f35,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X14] : (k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X14)) = k3_xboole_0(sK0,X14)) ) | ~spl3_5),
% 0.21/0.52    inference(superposition,[],[f32,f82])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    spl3_7 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f339,f80,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl3_7 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_5),
% 0.21/0.52    inference(forward_demodulation,[],[f329,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_xboole_0) | ~spl3_5),
% 0.21/0.52    inference(superposition,[],[f139,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f34,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f23,f26])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~spl3_8 | spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f125,f39,f129])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl3_1),
% 0.21/0.52    inference(resolution,[],[f37,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f26])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~spl3_7 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f101,f43,f104])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_2),
% 0.21/0.52    inference(resolution,[],[f29,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f43])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl3_5 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f77,f48,f80])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl3_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f27,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f48])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f48])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f26])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f20,f43,f39])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (21139)------------------------------
% 0.21/0.52  % (21139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21139)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (21139)Memory used [KB]: 6652
% 0.21/0.52  % (21139)Time elapsed: 0.079 s
% 0.21/0.52  % (21139)------------------------------
% 0.21/0.52  % (21139)------------------------------
% 0.21/0.53  % (21144)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (21132)Success in time 0.161 s
%------------------------------------------------------------------------------
