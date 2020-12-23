%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  62 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 (  94 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f60,f82,f182,f197])).

fof(f197,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl2_13 ),
    inference(unit_resulting_resolution,[],[f18,f181,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f181,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK1)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl2_13
  <=> r1_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f18,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f182,plain,
    ( ~ spl2_13
    | spl2_5 ),
    inference(avatar_split_clause,[],[f157,f79,f179])).

fof(f79,plain,
    ( spl2_5
  <=> r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f157,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK1)
    | spl2_5 ),
    inference(backward_demodulation,[],[f81,f66])).

fof(f66,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f25,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f26,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f81,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,
    ( ~ spl2_5
    | spl2_4 ),
    inference(avatar_split_clause,[],[f77,f57,f79])).

fof(f57,plain,
    ( spl2_4
  <=> r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

% (12258)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f77,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),sK1)
    | spl2_4 ),
    inference(forward_demodulation,[],[f76,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f76,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,sK1)))),sK1)
    | spl2_4 ),
    inference(forward_demodulation,[],[f75,f25])).

fof(f75,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),sK1)
    | spl2_4 ),
    inference(forward_demodulation,[],[f59,f25])).

fof(f59,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f60,plain,
    ( ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f45,f29,f57])).

fof(f29,plain,
    ( spl2_1
  <=> r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),sK1)
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f31,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f31,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.44  % (12264)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.44  % (12262)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.44  % (12270)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.44  % (12260)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.45  % (12267)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.45  % (12254)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.45  % (12260)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % (12256)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.45  % (12269)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f198,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f32,f60,f82,f182,f197])).
% 0.22/0.45  fof(f197,plain,(
% 0.22/0.45    spl2_13),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f193])).
% 0.22/0.45  fof(f193,plain,(
% 0.22/0.45    $false | spl2_13),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f18,f181,f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.45  fof(f181,plain,(
% 0.22/0.45    ~r1_xboole_0(k1_xboole_0,sK1) | spl2_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f179])).
% 0.22/0.45  fof(f179,plain,(
% 0.22/0.45    spl2_13 <=> r1_xboole_0(k1_xboole_0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.45  fof(f182,plain,(
% 0.22/0.45    ~spl2_13 | spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f157,f79,f179])).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    spl2_5 <=> r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.45  fof(f157,plain,(
% 0.22/0.45    ~r1_xboole_0(k1_xboole_0,sK1) | spl2_5),
% 0.22/0.45    inference(backward_demodulation,[],[f81,f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.22/0.45    inference(superposition,[],[f25,f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(forward_demodulation,[],[f26,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f19,f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),sK1) | spl2_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f79])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    ~spl2_5 | spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f77,f57,f79])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    spl2_4 <=> r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.45  % (12258)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),sK1) | spl2_4),
% 0.22/0.45    inference(forward_demodulation,[],[f76,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.45    inference(rectify,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,sK1)))),sK1) | spl2_4),
% 0.22/0.45    inference(forward_demodulation,[],[f75,f25])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),sK1) | spl2_4),
% 0.22/0.45    inference(forward_demodulation,[],[f59,f25])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),sK1) | spl2_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f57])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ~spl2_4 | spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f45,f29,f57])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    spl2_1 <=> r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),sK1) | spl2_1),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f31,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f24,f22])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) | spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f29])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ~spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f17,f29])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.45    inference(ennf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.45    inference(negated_conjecture,[],[f9])).
% 0.22/0.45  fof(f9,conjecture,(
% 0.22/0.45    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (12260)------------------------------
% 0.22/0.45  % (12260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (12260)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (12260)Memory used [KB]: 6268
% 0.22/0.45  % (12260)Time elapsed: 0.045 s
% 0.22/0.45  % (12260)------------------------------
% 0.22/0.45  % (12260)------------------------------
% 0.22/0.45  % (12253)Success in time 0.093 s
%------------------------------------------------------------------------------
