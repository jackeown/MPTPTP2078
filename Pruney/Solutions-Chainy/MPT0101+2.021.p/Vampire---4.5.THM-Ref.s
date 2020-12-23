%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 118 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :   83 ( 158 expanded)
%              Number of equality atoms :   43 ( 103 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2086,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f855,f2084])).

fof(f2084,plain,(
    ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f2075])).

fof(f2075,plain,
    ( $false
    | ~ spl2_30 ),
    inference(resolution,[],[f2062,f767])).

fof(f767,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f766])).

fof(f766,plain,
    ( spl2_30
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f2062,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f2061])).

fof(f2061,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2060,f83])).

fof(f83,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f29,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f2060,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2048,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2048,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f749,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f749,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f704,f18])).

fof(f704,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f131,f47])).

fof(f47,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f43,f19])).

fof(f43,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f19,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f20,f18])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f131,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(forward_demodulation,[],[f28,f27])).

fof(f28,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f17,f22,f22,f21])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f855,plain,(
    spl2_30 ),
    inference(avatar_contradiction_clause,[],[f848])).

fof(f848,plain,
    ( $false
    | spl2_30 ),
    inference(resolution,[],[f844,f115])).

fof(f115,plain,(
    ! [X4,X5] : r1_xboole_0(k4_xboole_0(X4,X5),X5) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,X5) != k4_xboole_0(X4,X5)
      | r1_xboole_0(k4_xboole_0(X4,X5),X5) ) ),
    inference(superposition,[],[f26,f46])).

fof(f46,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    inference(forward_demodulation,[],[f41,f31])).

fof(f41,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f31,f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f844,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl2_30 ),
    inference(resolution,[],[f788,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f788,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | spl2_30 ),
    inference(resolution,[],[f768,f434])).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,X2),X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f132,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f27,f25])).

fof(f132,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f130,f18])).

fof(f130,plain,(
    ! [X10,X8,X9] : r1_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10) ),
    inference(superposition,[],[f115,f27])).

fof(f768,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))
    | spl2_30 ),
    inference(avatar_component_clause,[],[f766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:08:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.44  % (3199)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (3199)Refutation not found, incomplete strategy% (3199)------------------------------
% 0.21/0.44  % (3199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (3199)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (3199)Memory used [KB]: 10490
% 0.21/0.44  % (3199)Time elapsed: 0.003 s
% 0.21/0.44  % (3199)------------------------------
% 0.21/0.44  % (3199)------------------------------
% 0.21/0.46  % (3201)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (3197)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (3198)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (3192)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (3191)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (3205)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (3194)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (3193)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (3204)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (3200)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (3202)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (3189)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (3188)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (3190)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (3203)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (3195)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (3196)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (3192)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f2086,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f855,f2084])).
% 0.21/0.52  fof(f2084,plain,(
% 0.21/0.52    ~spl2_30),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f2075])).
% 0.21/0.52  fof(f2075,plain,(
% 0.21/0.52    $false | ~spl2_30),
% 0.21/0.52    inference(resolution,[],[f2062,f767])).
% 0.21/0.52  fof(f767,plain,(
% 0.21/0.52    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) | ~spl2_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f766])).
% 0.21/0.52  fof(f766,plain,(
% 0.21/0.52    spl2_30 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.52  fof(f2062,plain,(
% 0.21/0.52    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f2061])).
% 0.21/0.52  fof(f2061,plain,(
% 0.21/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f2060,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))) )),
% 0.21/0.52    inference(superposition,[],[f29,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f23,f22,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.21/0.52  fof(f2060,plain,(
% 0.21/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f2048,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.52  fof(f2048,plain,(
% 0.21/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.21/0.52    inference(superposition,[],[f749,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.52    inference(superposition,[],[f27,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.52  fof(f749,plain,(
% 0.21/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.21/0.52    inference(superposition,[],[f704,f18])).
% 0.21/0.52  fof(f704,plain,(
% 0.21/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.21/0.52    inference(backward_demodulation,[],[f131,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f43,f19])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 0.21/0.52    inference(superposition,[],[f19,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 0.21/0.52    inference(superposition,[],[f20,f18])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.21/0.52    inference(forward_demodulation,[],[f28,f27])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.21/0.52    inference(definition_unfolding,[],[f17,f22,f22,f21])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.53  fof(f855,plain,(
% 0.21/0.53    spl2_30),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f848])).
% 0.21/0.53  fof(f848,plain,(
% 0.21/0.53    $false | spl2_30),
% 0.21/0.53    inference(resolution,[],[f844,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ( ! [X4,X5] : (r1_xboole_0(k4_xboole_0(X4,X5),X5)) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k4_xboole_0(X4,X5) != k4_xboole_0(X4,X5) | r1_xboole_0(k4_xboole_0(X4,X5),X5)) )),
% 0.21/0.53    inference(superposition,[],[f26,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f41,f31])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4)) )),
% 0.21/0.53    inference(superposition,[],[f31,f19])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f844,plain,(
% 0.21/0.53    ~r1_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl2_30),
% 0.21/0.53    inference(resolution,[],[f788,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.53  fof(f788,plain,(
% 0.21/0.53    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | spl2_30),
% 0.21/0.53    inference(resolution,[],[f768,f434])).
% 0.21/0.53  fof(f434,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X2),X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f132,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f27,f25])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X1,X0)),X1)) )),
% 0.21/0.53    inference(superposition,[],[f130,f18])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X10,X8,X9] : (r1_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10)) )),
% 0.21/0.53    inference(superposition,[],[f115,f27])).
% 0.21/0.53  fof(f768,plain,(
% 0.21/0.53    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) | spl2_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f766])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (3192)------------------------------
% 0.21/0.53  % (3192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3192)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (3192)Memory used [KB]: 7291
% 0.21/0.53  % (3192)Time elapsed: 0.108 s
% 0.21/0.53  % (3192)------------------------------
% 0.21/0.53  % (3192)------------------------------
% 0.21/0.53  % (3187)Success in time 0.165 s
%------------------------------------------------------------------------------
