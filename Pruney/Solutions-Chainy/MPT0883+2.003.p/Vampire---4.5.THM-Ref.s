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
% DateTime   : Thu Dec  3 12:58:55 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   35 (  63 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  76 expanded)
%              Number of equality atoms :   35 (  66 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8098,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f7932])).

fof(f7932,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f7931])).

fof(f7931,plain,
    ( $false
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f7930])).

fof(f7930,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4))
    | spl5_1 ),
    inference(forward_demodulation,[],[f7850,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k2_tarski(k4_tarski(X0,X3),k4_tarski(X1,X3))) ),
    inference(forward_demodulation,[],[f88,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2)) ),
    inference(definition_unfolding,[],[f20,f14])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X3,X3))) ),
    inference(superposition,[],[f27,f25])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k2_tarski(X0,X0)),k2_zfmisc_1(X2,k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f22,f14,f14])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

fof(f7850,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) != k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3))),k2_tarski(sK4,sK4))
    | spl5_1 ),
    inference(superposition,[],[f32,f456])).

fof(f456,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X3,X4)),k2_tarski(X2,X2)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k2_tarski(k4_tarski(X3,X2),k4_tarski(X4,X2))) ),
    inference(superposition,[],[f52,f25])).

fof(f52,plain,(
    ! [X10,X8,X11,X9] : k2_zfmisc_1(k2_xboole_0(X11,k2_tarski(X8,X9)),k2_tarski(X10,X10)) = k2_xboole_0(k2_zfmisc_1(X11,k2_tarski(X10,X10)),k2_tarski(k4_tarski(X8,X10),k4_tarski(X9,X10))) ),
    inference(superposition,[],[f17,f25])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f32,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) = k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f33,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f30])).

fof(f24,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) ),
    inference(definition_unfolding,[],[f13,f15,f14,f23,f16,f16,f16,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

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
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:23:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.44  % (972)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.45  % (970)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.48  % (969)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.48  % (974)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.49  % (967)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.49  % (966)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.49  % (984)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.49  % (982)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.49  % (983)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.50  % (968)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.50  % (971)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.50  % (978)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.50  % (978)Refutation not found, incomplete strategy% (978)------------------------------
% 0.23/0.50  % (978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (978)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (978)Memory used [KB]: 10618
% 0.23/0.50  % (978)Time elapsed: 0.077 s
% 0.23/0.50  % (978)------------------------------
% 0.23/0.50  % (978)------------------------------
% 0.23/0.51  % (977)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.51  % (980)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.51  % (976)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.51  % (981)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.52  % (985)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.53  % (975)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.78/0.61  % (972)Refutation found. Thanks to Tanya!
% 1.78/0.61  % SZS status Theorem for theBenchmark
% 1.78/0.61  % SZS output start Proof for theBenchmark
% 1.78/0.61  fof(f8098,plain,(
% 1.78/0.61    $false),
% 1.78/0.61    inference(avatar_sat_refutation,[],[f33,f7932])).
% 1.78/0.61  fof(f7932,plain,(
% 1.78/0.61    spl5_1),
% 1.78/0.61    inference(avatar_contradiction_clause,[],[f7931])).
% 1.78/0.61  fof(f7931,plain,(
% 1.78/0.61    $false | spl5_1),
% 1.78/0.61    inference(trivial_inequality_removal,[],[f7930])).
% 1.78/0.61  fof(f7930,plain,(
% 1.78/0.61    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) | spl5_1),
% 1.78/0.61    inference(forward_demodulation,[],[f7850,f104])).
% 1.78/0.61  fof(f104,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k2_tarski(k4_tarski(X0,X3),k4_tarski(X1,X3)))) )),
% 1.78/0.61    inference(forward_demodulation,[],[f88,f25])).
% 1.78/0.61  fof(f25,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2))) )),
% 1.78/0.61    inference(definition_unfolding,[],[f20,f14])).
% 1.78/0.61  fof(f14,plain,(
% 1.78/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f2])).
% 1.78/0.61  fof(f2,axiom,(
% 1.78/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.78/0.61  fof(f20,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.78/0.61    inference(cnf_transformation,[],[f5])).
% 1.78/0.61  fof(f5,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.78/0.61  fof(f88,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X3,X3)))) )),
% 1.78/0.61    inference(superposition,[],[f27,f25])).
% 1.78/0.61  fof(f27,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k2_tarski(X0,X0)),k2_zfmisc_1(X2,k2_tarski(X1,X1)))) )),
% 1.78/0.61    inference(definition_unfolding,[],[f22,f14,f14])).
% 1.78/0.61  fof(f22,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))) )),
% 1.78/0.61    inference(cnf_transformation,[],[f4])).
% 1.78/0.61  fof(f4,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 1.78/0.61  fof(f7850,plain,(
% 1.78/0.61    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) != k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3))),k2_tarski(sK4,sK4)) | spl5_1),
% 1.78/0.61    inference(superposition,[],[f32,f456])).
% 1.78/0.61  fof(f456,plain,(
% 1.78/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X3,X4)),k2_tarski(X2,X2)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k2_tarski(k4_tarski(X3,X2),k4_tarski(X4,X2)))) )),
% 1.78/0.61    inference(superposition,[],[f52,f25])).
% 1.78/0.61  fof(f52,plain,(
% 1.78/0.61    ( ! [X10,X8,X11,X9] : (k2_zfmisc_1(k2_xboole_0(X11,k2_tarski(X8,X9)),k2_tarski(X10,X10)) = k2_xboole_0(k2_zfmisc_1(X11,k2_tarski(X10,X10)),k2_tarski(k4_tarski(X8,X10),k4_tarski(X9,X10)))) )),
% 1.78/0.61    inference(superposition,[],[f17,f25])).
% 1.78/0.61  fof(f17,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.78/0.61    inference(cnf_transformation,[],[f3])).
% 1.78/0.61  fof(f3,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.78/0.61  fof(f32,plain,(
% 1.78/0.61    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) | spl5_1),
% 1.78/0.61    inference(avatar_component_clause,[],[f30])).
% 1.78/0.61  fof(f30,plain,(
% 1.78/0.61    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) = k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)))),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.78/0.61  fof(f33,plain,(
% 1.78/0.61    ~spl5_1),
% 1.78/0.61    inference(avatar_split_clause,[],[f24,f30])).
% 1.78/0.61  fof(f24,plain,(
% 1.78/0.61    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK4)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)))),
% 1.78/0.61    inference(definition_unfolding,[],[f13,f15,f14,f23,f16,f16,f16,f16])).
% 1.78/0.61  fof(f16,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f6])).
% 1.78/0.61  fof(f6,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.78/0.61  fof(f23,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.78/0.61    inference(cnf_transformation,[],[f1])).
% 1.78/0.61  fof(f1,axiom,(
% 1.78/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.78/0.61  fof(f15,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f7])).
% 1.78/0.61  fof(f7,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.78/0.61  fof(f13,plain,(
% 1.78/0.61    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 1.78/0.61    inference(cnf_transformation,[],[f12])).
% 1.78/0.61  fof(f12,plain,(
% 1.78/0.61    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 1.78/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).
% 1.78/0.61  fof(f11,plain,(
% 1.78/0.61    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 1.78/0.61    introduced(choice_axiom,[])).
% 1.78/0.61  fof(f10,plain,(
% 1.78/0.61    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 1.78/0.61    inference(ennf_transformation,[],[f9])).
% 1.78/0.61  fof(f9,negated_conjecture,(
% 1.78/0.61    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 1.78/0.61    inference(negated_conjecture,[],[f8])).
% 1.78/0.61  fof(f8,conjecture,(
% 1.78/0.61    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_mcart_1)).
% 1.78/0.61  % SZS output end Proof for theBenchmark
% 1.78/0.61  % (972)------------------------------
% 1.78/0.61  % (972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (972)Termination reason: Refutation
% 1.78/0.61  
% 1.78/0.61  % (972)Memory used [KB]: 11897
% 1.78/0.61  % (972)Time elapsed: 0.168 s
% 1.78/0.61  % (972)------------------------------
% 1.78/0.61  % (972)------------------------------
% 1.78/0.61  % (954)Success in time 0.237 s
%------------------------------------------------------------------------------
