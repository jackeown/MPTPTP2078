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
% DateTime   : Thu Dec  3 12:29:53 EST 2020

% Result     : Theorem 26.54s
% Output     : Refutation 26.54s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 331 expanded)
%              Number of leaves         :   12 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :   85 ( 346 expanded)
%              Number of equality atoms :   72 ( 326 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99650,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f99424])).

fof(f99424,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f99417])).

fof(f99417,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f33,f99416])).

fof(f99416,plain,(
    ! [X76,X74,X75] : k4_xboole_0(k2_xboole_0(X74,X76),X75) = k2_xboole_0(k4_xboole_0(X74,X75),k4_xboole_0(X76,X75)) ),
    inference(backward_demodulation,[],[f96115,f99067])).

fof(f99067,plain,(
    ! [X103,X101,X102] : k4_xboole_0(k2_xboole_0(X102,X103),X101) = k2_xboole_0(k4_xboole_0(X102,X101),k4_xboole_0(k2_xboole_0(X102,X103),X101)) ),
    inference(superposition,[],[f75131,f98487])).

fof(f98487,plain,(
    ! [X670,X671,X672] : k2_xboole_0(X672,k4_xboole_0(X670,k4_xboole_0(k2_xboole_0(X670,X671),X672))) = X672 ),
    inference(forward_demodulation,[],[f98112,f72774])).

fof(f72774,plain,(
    ! [X107,X105,X106] : k4_xboole_0(X105,k4_xboole_0(k2_xboole_0(X105,X106),X107)) = k4_xboole_0(k2_xboole_0(X105,k4_xboole_0(X106,X107)),k4_xboole_0(k2_xboole_0(X105,X106),X107)) ),
    inference(superposition,[],[f24,f53597])).

fof(f53597,plain,(
    ! [X39,X37,X38] : k2_xboole_0(X38,k4_xboole_0(X39,X37)) = k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(X38,X39),X37)) ),
    inference(forward_demodulation,[],[f53596,f79])).

fof(f79,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f53596,plain,(
    ! [X39,X37,X38] : k2_xboole_0(X38,k4_xboole_0(X39,X37)) = k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(X37,k2_xboole_0(X38,X39)),X37)) ),
    inference(forward_demodulation,[],[f53595,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f53595,plain,(
    ! [X39,X37,X38] : k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(k2_xboole_0(X37,X38),X39),X37)) = k2_xboole_0(X38,k4_xboole_0(X39,X37)) ),
    inference(forward_demodulation,[],[f53172,f801])).

fof(f801,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X15,k4_xboole_0(X13,X14)) = k2_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15))) ),
    inference(superposition,[],[f25,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f53172,plain,(
    ! [X39,X37,X38] : k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(k2_xboole_0(X37,X38),X39),X37)) = k2_xboole_0(X38,k4_xboole_0(X39,k2_xboole_0(X37,X38))) ),
    inference(superposition,[],[f801,f79])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f98112,plain,(
    ! [X670,X671,X672] : k2_xboole_0(X672,k4_xboole_0(k2_xboole_0(X670,k4_xboole_0(X671,X672)),k4_xboole_0(k2_xboole_0(X670,X671),X672))) = X672 ),
    inference(superposition,[],[f73127,f56868])).

fof(f56868,plain,(
    ! [X318,X320,X319] : k4_xboole_0(k2_xboole_0(X319,k4_xboole_0(X320,X318)),X318) = k4_xboole_0(k2_xboole_0(X319,X320),X318) ),
    inference(forward_demodulation,[],[f56396,f79])).

fof(f56396,plain,(
    ! [X318,X320,X319] : k4_xboole_0(k2_xboole_0(X319,k4_xboole_0(X320,X318)),X318) = k4_xboole_0(k2_xboole_0(X318,k2_xboole_0(X319,X320)),X318) ),
    inference(superposition,[],[f79,f2321])).

fof(f2321,plain,(
    ! [X26,X24,X25] : k2_xboole_0(X24,k2_xboole_0(X25,X26)) = k2_xboole_0(X24,k2_xboole_0(X25,k4_xboole_0(X26,X24))) ),
    inference(forward_demodulation,[],[f2320,f29])).

fof(f2320,plain,(
    ! [X26,X24,X25] : k2_xboole_0(k2_xboole_0(X24,X25),X26) = k2_xboole_0(X24,k2_xboole_0(X25,k4_xboole_0(X26,X24))) ),
    inference(forward_demodulation,[],[f2221,f801])).

fof(f2221,plain,(
    ! [X26,X24,X25] : k2_xboole_0(k2_xboole_0(X24,X25),X26) = k2_xboole_0(X24,k2_xboole_0(X25,k4_xboole_0(X26,k2_xboole_0(X24,X25)))) ),
    inference(superposition,[],[f29,f25])).

fof(f73127,plain,(
    ! [X33,X34] : k2_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X33))) = X33 ),
    inference(forward_demodulation,[],[f73126,f156])).

fof(f156,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8 ),
    inference(forward_demodulation,[],[f139,f86])).

fof(f86,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f81,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f81,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f24,f19])).

fof(f139,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(X8,k1_xboole_0) ),
    inference(superposition,[],[f25,f47])).

fof(f47,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6) ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f73126,plain,(
    ! [X33,X34] : k2_xboole_0(X33,k4_xboole_0(X33,X34)) = k2_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X33))) ),
    inference(forward_demodulation,[],[f72712,f53560])).

fof(f53560,plain,(
    ! [X185,X184,X183] : k2_xboole_0(X184,k4_xboole_0(X185,k4_xboole_0(X183,X184))) = k2_xboole_0(X184,k4_xboole_0(X185,X183)) ),
    inference(forward_demodulation,[],[f53149,f53109])).

fof(f53109,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f801,f23])).

fof(f53149,plain,(
    ! [X185,X184,X183] : k2_xboole_0(X184,k4_xboole_0(X185,k4_xboole_0(X183,X184))) = k2_xboole_0(X184,k4_xboole_0(X185,k2_xboole_0(X184,X183))) ),
    inference(superposition,[],[f801,f3070])).

fof(f3070,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k2_xboole_0(k4_xboole_0(X20,X19),X19) ),
    inference(forward_demodulation,[],[f2981,f197])).

fof(f197,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f186,f25])).

fof(f186,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k2_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(superposition,[],[f25,f79])).

fof(f2981,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k2_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X20,X19),X19) ),
    inference(superposition,[],[f2675,f25])).

fof(f2675,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f2216,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f2216,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X11,k2_xboole_0(X9,X10)) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(superposition,[],[f29,f23])).

fof(f72712,plain,(
    ! [X33,X34] : k2_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X33))) = k2_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,X33))) ),
    inference(superposition,[],[f53597,f142])).

fof(f142,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f24,f25])).

fof(f75131,plain,(
    ! [X97,X95,X96] : k2_xboole_0(k4_xboole_0(X95,k2_xboole_0(X96,k4_xboole_0(X95,X97))),X97) = X97 ),
    inference(forward_demodulation,[],[f75130,f53109])).

fof(f75130,plain,(
    ! [X97,X95,X96] : k2_xboole_0(k4_xboole_0(X95,k2_xboole_0(X96,k4_xboole_0(X95,k2_xboole_0(X96,X97)))),X97) = X97 ),
    inference(forward_demodulation,[],[f74712,f28])).

fof(f74712,plain,(
    ! [X97,X95,X96] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X95,X96),k4_xboole_0(X95,k2_xboole_0(X96,X97))),X97) = X97 ),
    inference(superposition,[],[f73628,f28])).

fof(f73628,plain,(
    ! [X103,X102] : k2_xboole_0(k4_xboole_0(X103,k4_xboole_0(X103,X102)),X102) = X102 ),
    inference(superposition,[],[f371,f73127])).

fof(f371,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f197,f23])).

fof(f96115,plain,(
    ! [X76,X74,X75] : k2_xboole_0(k4_xboole_0(X74,X75),k4_xboole_0(X76,X75)) = k2_xboole_0(k4_xboole_0(X74,X75),k4_xboole_0(k2_xboole_0(X74,X76),X75)) ),
    inference(superposition,[],[f53597,f55998])).

fof(f55998,plain,(
    ! [X397,X399,X398] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X398,X397),X399),X397) = k4_xboole_0(k2_xboole_0(X398,X399),X397) ),
    inference(forward_demodulation,[],[f55554,f79])).

fof(f55554,plain,(
    ! [X397,X399,X398] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X398,X397),X399),X397) = k4_xboole_0(k2_xboole_0(X397,k2_xboole_0(X398,X399)),X397) ),
    inference(superposition,[],[f79,f2301])).

fof(f2301,plain,(
    ! [X19,X17,X18] : k2_xboole_0(X17,k2_xboole_0(X18,X19)) = k2_xboole_0(X17,k2_xboole_0(k4_xboole_0(X18,X17),X19)) ),
    inference(forward_demodulation,[],[f2205,f29])).

fof(f2205,plain,(
    ! [X19,X17,X18] : k2_xboole_0(k2_xboole_0(X17,X18),X19) = k2_xboole_0(X17,k2_xboole_0(k4_xboole_0(X18,X17),X19)) ),
    inference(superposition,[],[f29,f25])).

fof(f33,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (4272)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (4273)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (4267)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.44  % (4269)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.44  % (4268)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.45  % (4274)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.47  % (4277)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.47  % (4278)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.48  % (4276)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.49  % (4270)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.49  % (4271)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.49  % (4275)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 5.04/1.02  % (4268)Time limit reached!
% 5.04/1.02  % (4268)------------------------------
% 5.04/1.02  % (4268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.02  % (4268)Termination reason: Time limit
% 5.04/1.02  % (4268)Termination phase: Saturation
% 5.04/1.02  
% 5.04/1.02  % (4268)Memory used [KB]: 30703
% 5.04/1.02  % (4268)Time elapsed: 0.600 s
% 5.04/1.02  % (4268)------------------------------
% 5.04/1.02  % (4268)------------------------------
% 8.47/1.44  % (4267)Time limit reached!
% 8.47/1.44  % (4267)------------------------------
% 8.47/1.44  % (4267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.47/1.44  % (4267)Termination reason: Time limit
% 8.47/1.44  
% 8.47/1.44  % (4267)Memory used [KB]: 43368
% 8.47/1.44  % (4267)Time elapsed: 1.026 s
% 8.47/1.44  % (4267)------------------------------
% 8.47/1.44  % (4267)------------------------------
% 26.54/3.75  % (4274)Refutation found. Thanks to Tanya!
% 26.54/3.75  % SZS status Theorem for theBenchmark
% 26.54/3.75  % SZS output start Proof for theBenchmark
% 26.54/3.75  fof(f99650,plain,(
% 26.54/3.75    $false),
% 26.54/3.75    inference(avatar_sat_refutation,[],[f34,f99424])).
% 26.54/3.75  fof(f99424,plain,(
% 26.54/3.75    spl3_1),
% 26.54/3.75    inference(avatar_contradiction_clause,[],[f99417])).
% 26.54/3.75  fof(f99417,plain,(
% 26.54/3.75    $false | spl3_1),
% 26.54/3.75    inference(subsumption_resolution,[],[f33,f99416])).
% 26.54/3.75  fof(f99416,plain,(
% 26.54/3.75    ( ! [X76,X74,X75] : (k4_xboole_0(k2_xboole_0(X74,X76),X75) = k2_xboole_0(k4_xboole_0(X74,X75),k4_xboole_0(X76,X75))) )),
% 26.54/3.75    inference(backward_demodulation,[],[f96115,f99067])).
% 26.54/3.75  fof(f99067,plain,(
% 26.54/3.75    ( ! [X103,X101,X102] : (k4_xboole_0(k2_xboole_0(X102,X103),X101) = k2_xboole_0(k4_xboole_0(X102,X101),k4_xboole_0(k2_xboole_0(X102,X103),X101))) )),
% 26.54/3.75    inference(superposition,[],[f75131,f98487])).
% 26.54/3.75  fof(f98487,plain,(
% 26.54/3.75    ( ! [X670,X671,X672] : (k2_xboole_0(X672,k4_xboole_0(X670,k4_xboole_0(k2_xboole_0(X670,X671),X672))) = X672) )),
% 26.54/3.75    inference(forward_demodulation,[],[f98112,f72774])).
% 26.54/3.75  fof(f72774,plain,(
% 26.54/3.75    ( ! [X107,X105,X106] : (k4_xboole_0(X105,k4_xboole_0(k2_xboole_0(X105,X106),X107)) = k4_xboole_0(k2_xboole_0(X105,k4_xboole_0(X106,X107)),k4_xboole_0(k2_xboole_0(X105,X106),X107))) )),
% 26.54/3.75    inference(superposition,[],[f24,f53597])).
% 26.54/3.75  fof(f53597,plain,(
% 26.54/3.75    ( ! [X39,X37,X38] : (k2_xboole_0(X38,k4_xboole_0(X39,X37)) = k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(X38,X39),X37))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f53596,f79])).
% 26.54/3.75  fof(f79,plain,(
% 26.54/3.75    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 26.54/3.75    inference(superposition,[],[f24,f23])).
% 26.54/3.75  fof(f23,plain,(
% 26.54/3.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 26.54/3.75    inference(cnf_transformation,[],[f1])).
% 26.54/3.75  fof(f1,axiom,(
% 26.54/3.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 26.54/3.75  fof(f53596,plain,(
% 26.54/3.75    ( ! [X39,X37,X38] : (k2_xboole_0(X38,k4_xboole_0(X39,X37)) = k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(X37,k2_xboole_0(X38,X39)),X37))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f53595,f29])).
% 26.54/3.75  fof(f29,plain,(
% 26.54/3.75    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 26.54/3.75    inference(cnf_transformation,[],[f9])).
% 26.54/3.75  fof(f9,axiom,(
% 26.54/3.75    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 26.54/3.75  fof(f53595,plain,(
% 26.54/3.75    ( ! [X39,X37,X38] : (k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(k2_xboole_0(X37,X38),X39),X37)) = k2_xboole_0(X38,k4_xboole_0(X39,X37))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f53172,f801])).
% 26.54/3.75  fof(f801,plain,(
% 26.54/3.75    ( ! [X14,X15,X13] : (k2_xboole_0(X15,k4_xboole_0(X13,X14)) = k2_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15)))) )),
% 26.54/3.75    inference(superposition,[],[f25,f28])).
% 26.54/3.75  fof(f28,plain,(
% 26.54/3.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 26.54/3.75    inference(cnf_transformation,[],[f8])).
% 26.54/3.75  fof(f8,axiom,(
% 26.54/3.75    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 26.54/3.75  fof(f25,plain,(
% 26.54/3.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 26.54/3.75    inference(cnf_transformation,[],[f5])).
% 26.54/3.75  fof(f5,axiom,(
% 26.54/3.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 26.54/3.75  fof(f53172,plain,(
% 26.54/3.75    ( ! [X39,X37,X38] : (k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(k2_xboole_0(X37,X38),X39),X37)) = k2_xboole_0(X38,k4_xboole_0(X39,k2_xboole_0(X37,X38)))) )),
% 26.54/3.75    inference(superposition,[],[f801,f79])).
% 26.54/3.75  fof(f24,plain,(
% 26.54/3.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 26.54/3.75    inference(cnf_transformation,[],[f7])).
% 26.54/3.75  fof(f7,axiom,(
% 26.54/3.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 26.54/3.75  fof(f98112,plain,(
% 26.54/3.75    ( ! [X670,X671,X672] : (k2_xboole_0(X672,k4_xboole_0(k2_xboole_0(X670,k4_xboole_0(X671,X672)),k4_xboole_0(k2_xboole_0(X670,X671),X672))) = X672) )),
% 26.54/3.75    inference(superposition,[],[f73127,f56868])).
% 26.54/3.75  fof(f56868,plain,(
% 26.54/3.75    ( ! [X318,X320,X319] : (k4_xboole_0(k2_xboole_0(X319,k4_xboole_0(X320,X318)),X318) = k4_xboole_0(k2_xboole_0(X319,X320),X318)) )),
% 26.54/3.75    inference(forward_demodulation,[],[f56396,f79])).
% 26.54/3.75  fof(f56396,plain,(
% 26.54/3.75    ( ! [X318,X320,X319] : (k4_xboole_0(k2_xboole_0(X319,k4_xboole_0(X320,X318)),X318) = k4_xboole_0(k2_xboole_0(X318,k2_xboole_0(X319,X320)),X318)) )),
% 26.54/3.75    inference(superposition,[],[f79,f2321])).
% 26.54/3.75  fof(f2321,plain,(
% 26.54/3.75    ( ! [X26,X24,X25] : (k2_xboole_0(X24,k2_xboole_0(X25,X26)) = k2_xboole_0(X24,k2_xboole_0(X25,k4_xboole_0(X26,X24)))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f2320,f29])).
% 26.54/3.75  fof(f2320,plain,(
% 26.54/3.75    ( ! [X26,X24,X25] : (k2_xboole_0(k2_xboole_0(X24,X25),X26) = k2_xboole_0(X24,k2_xboole_0(X25,k4_xboole_0(X26,X24)))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f2221,f801])).
% 26.54/3.75  fof(f2221,plain,(
% 26.54/3.75    ( ! [X26,X24,X25] : (k2_xboole_0(k2_xboole_0(X24,X25),X26) = k2_xboole_0(X24,k2_xboole_0(X25,k4_xboole_0(X26,k2_xboole_0(X24,X25))))) )),
% 26.54/3.75    inference(superposition,[],[f29,f25])).
% 26.54/3.75  fof(f73127,plain,(
% 26.54/3.75    ( ! [X33,X34] : (k2_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X33))) = X33) )),
% 26.54/3.75    inference(forward_demodulation,[],[f73126,f156])).
% 26.54/3.75  fof(f156,plain,(
% 26.54/3.75    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8) )),
% 26.54/3.75    inference(forward_demodulation,[],[f139,f86])).
% 26.54/3.75  fof(f86,plain,(
% 26.54/3.75    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 26.54/3.75    inference(forward_demodulation,[],[f81,f19])).
% 26.54/3.75  fof(f19,plain,(
% 26.54/3.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 26.54/3.75    inference(cnf_transformation,[],[f6])).
% 26.54/3.75  fof(f6,axiom,(
% 26.54/3.75    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 26.54/3.75  fof(f81,plain,(
% 26.54/3.75    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 26.54/3.75    inference(superposition,[],[f24,f19])).
% 26.54/3.75  fof(f139,plain,(
% 26.54/3.75    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(X8,k1_xboole_0)) )),
% 26.54/3.75    inference(superposition,[],[f25,f47])).
% 26.54/3.75  fof(f47,plain,(
% 26.54/3.75    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6)) )),
% 26.54/3.75    inference(resolution,[],[f27,f22])).
% 26.54/3.75  fof(f22,plain,(
% 26.54/3.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 26.54/3.75    inference(cnf_transformation,[],[f4])).
% 26.54/3.75  fof(f4,axiom,(
% 26.54/3.75    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 26.54/3.75  fof(f27,plain,(
% 26.54/3.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 26.54/3.75    inference(cnf_transformation,[],[f17])).
% 26.54/3.75  fof(f17,plain,(
% 26.54/3.75    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 26.54/3.75    inference(nnf_transformation,[],[f3])).
% 26.54/3.75  fof(f3,axiom,(
% 26.54/3.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 26.54/3.75  fof(f73126,plain,(
% 26.54/3.75    ( ! [X33,X34] : (k2_xboole_0(X33,k4_xboole_0(X33,X34)) = k2_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X33)))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f72712,f53560])).
% 26.54/3.75  fof(f53560,plain,(
% 26.54/3.75    ( ! [X185,X184,X183] : (k2_xboole_0(X184,k4_xboole_0(X185,k4_xboole_0(X183,X184))) = k2_xboole_0(X184,k4_xboole_0(X185,X183))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f53149,f53109])).
% 26.54/3.75  fof(f53109,plain,(
% 26.54/3.75    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 26.54/3.75    inference(superposition,[],[f801,f23])).
% 26.54/3.75  fof(f53149,plain,(
% 26.54/3.75    ( ! [X185,X184,X183] : (k2_xboole_0(X184,k4_xboole_0(X185,k4_xboole_0(X183,X184))) = k2_xboole_0(X184,k4_xboole_0(X185,k2_xboole_0(X184,X183)))) )),
% 26.54/3.75    inference(superposition,[],[f801,f3070])).
% 26.54/3.75  fof(f3070,plain,(
% 26.54/3.75    ( ! [X19,X20] : (k2_xboole_0(X19,X20) = k2_xboole_0(k4_xboole_0(X20,X19),X19)) )),
% 26.54/3.75    inference(forward_demodulation,[],[f2981,f197])).
% 26.54/3.75  fof(f197,plain,(
% 26.54/3.75    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f186,f25])).
% 26.54/3.75  fof(f186,plain,(
% 26.54/3.75    ( ! [X4,X3] : (k2_xboole_0(X3,k2_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 26.54/3.75    inference(superposition,[],[f25,f79])).
% 26.54/3.75  fof(f2981,plain,(
% 26.54/3.75    ( ! [X19,X20] : (k2_xboole_0(X19,k2_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X20,X19),X19)) )),
% 26.54/3.75    inference(superposition,[],[f2675,f25])).
% 26.54/3.75  fof(f2675,plain,(
% 26.54/3.75    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 26.54/3.75    inference(superposition,[],[f2216,f20])).
% 26.54/3.75  fof(f20,plain,(
% 26.54/3.75    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 26.54/3.75    inference(cnf_transformation,[],[f13])).
% 26.54/3.75  fof(f13,plain,(
% 26.54/3.75    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 26.54/3.75    inference(rectify,[],[f2])).
% 26.54/3.75  fof(f2,axiom,(
% 26.54/3.75    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 26.54/3.75  fof(f2216,plain,(
% 26.54/3.75    ( ! [X10,X11,X9] : (k2_xboole_0(X11,k2_xboole_0(X9,X10)) = k2_xboole_0(X9,k2_xboole_0(X10,X11))) )),
% 26.54/3.75    inference(superposition,[],[f29,f23])).
% 26.54/3.75  fof(f72712,plain,(
% 26.54/3.75    ( ! [X33,X34] : (k2_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X33))) = k2_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,X33)))) )),
% 26.54/3.75    inference(superposition,[],[f53597,f142])).
% 26.54/3.75  fof(f142,plain,(
% 26.54/3.75    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) )),
% 26.54/3.75    inference(superposition,[],[f24,f25])).
% 26.54/3.75  fof(f75131,plain,(
% 26.54/3.75    ( ! [X97,X95,X96] : (k2_xboole_0(k4_xboole_0(X95,k2_xboole_0(X96,k4_xboole_0(X95,X97))),X97) = X97) )),
% 26.54/3.75    inference(forward_demodulation,[],[f75130,f53109])).
% 26.54/3.75  fof(f75130,plain,(
% 26.54/3.75    ( ! [X97,X95,X96] : (k2_xboole_0(k4_xboole_0(X95,k2_xboole_0(X96,k4_xboole_0(X95,k2_xboole_0(X96,X97)))),X97) = X97) )),
% 26.54/3.75    inference(forward_demodulation,[],[f74712,f28])).
% 26.54/3.75  fof(f74712,plain,(
% 26.54/3.75    ( ! [X97,X95,X96] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X95,X96),k4_xboole_0(X95,k2_xboole_0(X96,X97))),X97) = X97) )),
% 26.54/3.75    inference(superposition,[],[f73628,f28])).
% 26.54/3.75  fof(f73628,plain,(
% 26.54/3.75    ( ! [X103,X102] : (k2_xboole_0(k4_xboole_0(X103,k4_xboole_0(X103,X102)),X102) = X102) )),
% 26.54/3.75    inference(superposition,[],[f371,f73127])).
% 26.54/3.75  fof(f371,plain,(
% 26.54/3.75    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 26.54/3.75    inference(superposition,[],[f197,f23])).
% 26.54/3.75  fof(f96115,plain,(
% 26.54/3.75    ( ! [X76,X74,X75] : (k2_xboole_0(k4_xboole_0(X74,X75),k4_xboole_0(X76,X75)) = k2_xboole_0(k4_xboole_0(X74,X75),k4_xboole_0(k2_xboole_0(X74,X76),X75))) )),
% 26.54/3.75    inference(superposition,[],[f53597,f55998])).
% 26.54/3.75  fof(f55998,plain,(
% 26.54/3.75    ( ! [X397,X399,X398] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X398,X397),X399),X397) = k4_xboole_0(k2_xboole_0(X398,X399),X397)) )),
% 26.54/3.75    inference(forward_demodulation,[],[f55554,f79])).
% 26.54/3.75  fof(f55554,plain,(
% 26.54/3.75    ( ! [X397,X399,X398] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X398,X397),X399),X397) = k4_xboole_0(k2_xboole_0(X397,k2_xboole_0(X398,X399)),X397)) )),
% 26.54/3.75    inference(superposition,[],[f79,f2301])).
% 26.54/3.75  fof(f2301,plain,(
% 26.54/3.75    ( ! [X19,X17,X18] : (k2_xboole_0(X17,k2_xboole_0(X18,X19)) = k2_xboole_0(X17,k2_xboole_0(k4_xboole_0(X18,X17),X19))) )),
% 26.54/3.75    inference(forward_demodulation,[],[f2205,f29])).
% 26.54/3.75  fof(f2205,plain,(
% 26.54/3.75    ( ! [X19,X17,X18] : (k2_xboole_0(k2_xboole_0(X17,X18),X19) = k2_xboole_0(X17,k2_xboole_0(k4_xboole_0(X18,X17),X19))) )),
% 26.54/3.75    inference(superposition,[],[f29,f25])).
% 26.54/3.75  fof(f33,plain,(
% 26.54/3.75    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl3_1),
% 26.54/3.75    inference(avatar_component_clause,[],[f31])).
% 26.54/3.75  fof(f31,plain,(
% 26.54/3.75    spl3_1 <=> k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 26.54/3.75    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 26.54/3.75  fof(f34,plain,(
% 26.54/3.75    ~spl3_1),
% 26.54/3.75    inference(avatar_split_clause,[],[f18,f31])).
% 26.54/3.75  fof(f18,plain,(
% 26.54/3.75    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 26.54/3.75    inference(cnf_transformation,[],[f16])).
% 26.54/3.75  fof(f16,plain,(
% 26.54/3.75    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 26.54/3.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 26.54/3.75  fof(f15,plain,(
% 26.54/3.75    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 26.54/3.75    introduced(choice_axiom,[])).
% 26.54/3.75  fof(f14,plain,(
% 26.54/3.75    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 26.54/3.75    inference(ennf_transformation,[],[f12])).
% 26.54/3.75  fof(f12,negated_conjecture,(
% 26.54/3.75    ~! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 26.54/3.75    inference(negated_conjecture,[],[f11])).
% 26.54/3.75  fof(f11,conjecture,(
% 26.54/3.75    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 26.54/3.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 26.54/3.75  % SZS output end Proof for theBenchmark
% 26.54/3.75  % (4274)------------------------------
% 26.54/3.75  % (4274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.54/3.75  % (4274)Termination reason: Refutation
% 26.54/3.75  
% 26.54/3.75  % (4274)Memory used [KB]: 90318
% 26.54/3.75  % (4274)Time elapsed: 3.298 s
% 26.54/3.75  % (4274)------------------------------
% 26.54/3.75  % (4274)------------------------------
% 27.13/3.76  % (4266)Success in time 3.395 s
%------------------------------------------------------------------------------
