%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  74 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  90 expanded)
%              Number of equality atoms :   32 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f66,f89])).

fof(f89,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))
    | spl5_2 ),
    inference(forward_demodulation,[],[f82,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f82,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3))),k1_tarski(sK4))
    | spl5_2 ),
    inference(superposition,[],[f65,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) = k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f66,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f61,f26,f63])).

fof(f26,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) = k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f61,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f54,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X0,X2),X3)),k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))) ),
    inference(definition_unfolding,[],[f21,f16,f15,f15,f17,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).

fof(f54,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4)))
    | spl5_1 ),
    inference(backward_demodulation,[],[f28,f24])).

fof(f28,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f29,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f26])).

fof(f23,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4)))) ),
    inference(definition_unfolding,[],[f13,f16,f15,f15,f22,f17,f17,f17,f17])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f20,f15,f15])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f13,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:51:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.40  % (16695)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.41  % (16711)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.42  % (16697)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.43  % (16707)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.44  % (16705)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.44  % (16696)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (16700)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (16701)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (16706)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (16706)Refutation not found, incomplete strategy% (16706)------------------------------
% 0.20/0.47  % (16706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16706)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (16706)Memory used [KB]: 10618
% 0.20/0.47  % (16706)Time elapsed: 0.071 s
% 0.20/0.47  % (16706)------------------------------
% 0.20/0.47  % (16706)------------------------------
% 0.20/0.47  % (16701)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f29,f66,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl5_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    $false | spl5_2),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) | spl5_2),
% 0.20/0.47    inference(forward_demodulation,[],[f82,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3))),k1_tarski(sK4)) | spl5_2),
% 0.20/0.47    inference(superposition,[],[f65,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4))) | spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl5_2 <=> k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) = k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ~spl5_2 | spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f61,f26,f63])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) = k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4))) | spl5_1),
% 0.20/0.47    inference(forward_demodulation,[],[f54,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X0,X2),X3)),k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f21,f16,f15,f15,f17,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4))) | spl5_1),
% 0.20/0.47    inference(backward_demodulation,[],[f28,f24])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4)))) | spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f26])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ~spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f23,f26])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4))))),
% 0.20/0.47    inference(definition_unfolding,[],[f13,f16,f15,f15,f22,f17,f17,f17,f17])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f20,f15,f15])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_mcart_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (16701)------------------------------
% 0.20/0.47  % (16701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16701)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (16701)Memory used [KB]: 6140
% 0.20/0.47  % (16701)Time elapsed: 0.045 s
% 0.20/0.47  % (16701)------------------------------
% 0.20/0.47  % (16701)------------------------------
% 0.20/0.47  % (16692)Success in time 0.126 s
%------------------------------------------------------------------------------
