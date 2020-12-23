%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 100 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 121 expanded)
%              Number of equality atoms :   41 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f45,f58])).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f55,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f55,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK2))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f54,f28])).

fof(f28,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f16,f13])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f54,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f53,f28])).

fof(f53,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK1)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f52,f13])).

fof(f52,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK3))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f51,f28])).

fof(f51,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK1)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f50,f28])).

fof(f50,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f49,f28])).

fof(f49,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f46,f28])).

fof(f46,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))
    | spl5_2 ),
    inference(superposition,[],[f44,f16])).

fof(f44,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_2
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f45,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f40,f35,f42])).

fof(f35,plain,
    ( spl5_1
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f40,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f39,f28])).

% (30514)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f39,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK2)))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f37,f28])).

fof(f37,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f38,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f35])).

fof(f24,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))) ),
    inference(forward_demodulation,[],[f23,f13])).

fof(f23,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)))) ),
    inference(backward_demodulation,[],[f22,f16])).

fof(f22,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))) ),
    inference(definition_unfolding,[],[f12,f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(definition_unfolding,[],[f18,f19,f14])).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f12,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.44  % (30499)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (30507)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (30504)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (30501)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (30500)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (30515)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (30505)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (30515)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f38,f45,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    $false | spl5_2),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) | spl5_2),
% 0.20/0.48    inference(forward_demodulation,[],[f55,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK2)))) | spl5_2),
% 0.20/0.48    inference(forward_demodulation,[],[f54,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 0.20/0.48    inference(superposition,[],[f16,f13])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) | spl5_2),
% 0.20/0.48    inference(forward_demodulation,[],[f53,f28])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK1))))) | spl5_2),
% 0.20/0.48    inference(forward_demodulation,[],[f52,f13])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK3)))) | spl5_2),
% 0.20/0.48    inference(forward_demodulation,[],[f51,f28])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK1))))) | spl5_2),
% 0.20/0.48    inference(forward_demodulation,[],[f50,f28])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) | spl5_2),
% 0.20/0.48    inference(forward_demodulation,[],[f49,f28])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)))) | spl5_2),
% 0.20/0.48    inference(forward_demodulation,[],[f46,f28])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) | spl5_2),
% 0.20/0.48    inference(superposition,[],[f44,f16])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) | spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl5_2 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ~spl5_2 | spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f35,f42])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    spl5_1 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))) | spl5_1),
% 0.20/0.48    inference(forward_demodulation,[],[f39,f28])).
% 0.20/0.48  % (30514)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK2))))) | spl5_1),
% 0.20/0.48    inference(forward_demodulation,[],[f37,f28])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))) | spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f35])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f35])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))))),
% 0.20/0.48    inference(forward_demodulation,[],[f23,f13])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4))))),
% 0.20/0.48    inference(backward_demodulation,[],[f22,f16])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)))),
% 0.20/0.48    inference(definition_unfolding,[],[f12,f20,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f17,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f15,f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f18,f19,f14])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (30515)------------------------------
% 0.20/0.48  % (30515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30515)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (30515)Memory used [KB]: 10618
% 0.20/0.48  % (30515)Time elapsed: 0.007 s
% 0.20/0.48  % (30515)------------------------------
% 0.20/0.48  % (30515)------------------------------
% 0.20/0.48  % (30495)Success in time 0.123 s
%------------------------------------------------------------------------------
