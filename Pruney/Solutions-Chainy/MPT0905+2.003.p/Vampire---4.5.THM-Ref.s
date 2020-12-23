%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  52 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   32 (  56 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(forward_demodulation,[],[f156,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f156,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k1_tarski(k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)) ),
    inference(superposition,[],[f139,f38])).

fof(f38,plain,(
    ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f32,f14])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X4)) ),
    inference(superposition,[],[f18,f14])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f139,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k2_zfmisc_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f138,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f138,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k2_zfmisc_1(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_tarski(sK3)) ),
    inference(superposition,[],[f106,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2) ),
    inference(superposition,[],[f16,f38])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f106,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k3_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(superposition,[],[f13,f59])).

fof(f59,plain,(
    ! [X14,X12,X13,X11] : k4_zfmisc_1(k1_tarski(X11),k1_tarski(X12),X13,X14) = k3_zfmisc_1(k1_tarski(k4_tarski(X11,X12)),X13,X14) ),
    inference(superposition,[],[f23,f38])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(forward_demodulation,[],[f22,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(superposition,[],[f16,f16])).

fof(f13,plain,(
    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))
   => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:38:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (25329)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (25340)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  % (25329)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (25326)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (25336)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.46  % (25338)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (25343)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.47  % (25341)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.47  % (25330)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (25339)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.47  % (25334)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.47  % (25332)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.48  % (25331)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f158,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(trivial_inequality_removal,[],[f157])).
% 0.19/0.48  fof(f157,plain,(
% 0.19/0.48    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.19/0.48    inference(forward_demodulation,[],[f156,f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.19/0.48  fof(f156,plain,(
% 0.19/0.48    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k1_tarski(k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3))),
% 0.19/0.48    inference(superposition,[],[f139,f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))) )),
% 0.19/0.48    inference(forward_demodulation,[],[f32,f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X4))) )),
% 0.19/0.48    inference(superposition,[],[f18,f14])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.19/0.48  fof(f139,plain,(
% 0.19/0.48    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k2_zfmisc_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)),k1_tarski(sK3))),
% 0.19/0.48    inference(forward_demodulation,[],[f138,f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.19/0.48  fof(f138,plain,(
% 0.19/0.48    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k2_zfmisc_1(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_tarski(sK3))),
% 0.19/0.48    inference(superposition,[],[f106,f40])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2)) )),
% 0.19/0.48    inference(superposition,[],[f16,f38])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.19/0.48  fof(f106,plain,(
% 0.19/0.48    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k3_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2),k1_tarski(sK3))),
% 0.19/0.48    inference(superposition,[],[f13,f59])).
% 0.19/0.48  fof(f59,plain,(
% 0.19/0.48    ( ! [X14,X12,X13,X11] : (k4_zfmisc_1(k1_tarski(X11),k1_tarski(X12),X13,X14) = k3_zfmisc_1(k1_tarski(k4_tarski(X11,X12)),X13,X14)) )),
% 0.19/0.48    inference(superposition,[],[f23,f38])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f22,f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) )),
% 0.19/0.48    inference(superposition,[],[f16,f16])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.19/0.48    inference(negated_conjecture,[],[f8])).
% 0.19/0.48  fof(f8,conjecture,(
% 0.19/0.48    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_mcart_1)).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (25329)------------------------------
% 0.19/0.48  % (25329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (25329)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (25329)Memory used [KB]: 1663
% 0.19/0.48  % (25329)Time elapsed: 0.056 s
% 0.19/0.48  % (25329)------------------------------
% 0.19/0.48  % (25329)------------------------------
% 0.19/0.48  % (25333)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.48  % (25335)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.48  % (25327)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.48  % (25325)Success in time 0.13 s
%------------------------------------------------------------------------------
