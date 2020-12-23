%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:08 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 113 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :   55 ( 236 expanded)
%              Number of equality atoms :   35 ( 113 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) ),
    inference(forward_demodulation,[],[f109,f30])).

fof(f30,plain,(
    sK2 = k5_xboole_0(k5_xboole_0(sK2,sK3),sK3) ),
    inference(forward_demodulation,[],[f28,f26])).

fof(f26,plain,(
    sK3 = k2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f19,f14])).

fof(f14,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f28,plain,(
    sK2 = k5_xboole_0(k5_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f23,f26])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f109,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(k5_xboole_0(sK2,sK3),sK3)) ),
    inference(forward_demodulation,[],[f108,f26])).

fof(f108,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(k5_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f99,f22])).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f18,f18])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f99,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(k5_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[],[f21,f89])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)),k2_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(sK0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f58,f29])).

fof(f29,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f27,f25])).

fof(f25,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f19,f13])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f23,f25])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)),k2_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f24,f25])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f20,f18,f18,f18])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f21,plain,(
    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f15,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:37:33 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.44  % (27768)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.18/0.44  % (27755)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.44  % (27753)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.44  % (27764)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.44  % (27751)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.18/0.45  % (27750)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.18/0.45  % (27766)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.45  % (27764)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.45  % (27757)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.18/0.45  % (27752)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f111,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(trivial_inequality_removal,[],[f110])).
% 0.18/0.46  fof(f110,plain,(
% 0.18/0.46    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)),
% 0.18/0.46    inference(forward_demodulation,[],[f109,f30])).
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    sK2 = k5_xboole_0(k5_xboole_0(sK2,sK3),sK3)),
% 0.18/0.46    inference(forward_demodulation,[],[f28,f26])).
% 0.18/0.46  fof(f26,plain,(
% 0.18/0.46    sK3 = k2_xboole_0(sK2,sK3)),
% 0.18/0.46    inference(resolution,[],[f19,f14])).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    r1_tarski(sK2,sK3)),
% 0.18/0.46    inference(cnf_transformation,[],[f12])).
% 0.18/0.46  fof(f12,plain,(
% 0.18/0.46    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).
% 0.18/0.46  fof(f11,plain,(
% 0.18/0.46    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f9,plain,(
% 0.18/0.46    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.18/0.46    inference(flattening,[],[f8])).
% 0.18/0.46  fof(f8,plain,(
% 0.18/0.46    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.18/0.46    inference(ennf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,negated_conjecture,(
% 0.18/0.46    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.18/0.46    inference(negated_conjecture,[],[f6])).
% 0.18/0.46  fof(f6,conjecture,(
% 0.18/0.46    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.18/0.46    inference(cnf_transformation,[],[f10])).
% 0.18/0.46  fof(f10,plain,(
% 0.18/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.18/0.46  fof(f28,plain,(
% 0.18/0.46    sK2 = k5_xboole_0(k5_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3))),
% 0.18/0.46    inference(superposition,[],[f23,f26])).
% 0.18/0.46  fof(f23,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.18/0.46    inference(definition_unfolding,[],[f17,f18])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.18/0.46  fof(f109,plain,(
% 0.18/0.46    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(k5_xboole_0(sK2,sK3),sK3))),
% 0.18/0.46    inference(forward_demodulation,[],[f108,f26])).
% 0.18/0.46  fof(f108,plain,(
% 0.18/0.46    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(k5_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)))),
% 0.18/0.46    inference(forward_demodulation,[],[f99,f22])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 0.18/0.46    inference(definition_unfolding,[],[f16,f18,f18])).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.18/0.46  fof(f99,plain,(
% 0.18/0.46    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(k5_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)))),
% 0.18/0.46    inference(superposition,[],[f21,f89])).
% 0.18/0.46  fof(f89,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)),k2_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(sK0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 0.18/0.46    inference(forward_demodulation,[],[f58,f29])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    sK0 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.18/0.46    inference(forward_demodulation,[],[f27,f25])).
% 0.18/0.46  fof(f25,plain,(
% 0.18/0.46    sK1 = k2_xboole_0(sK0,sK1)),
% 0.18/0.46    inference(resolution,[],[f19,f13])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    r1_tarski(sK0,sK1)),
% 0.18/0.46    inference(cnf_transformation,[],[f12])).
% 0.18/0.46  fof(f27,plain,(
% 0.18/0.46    sK0 = k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.18/0.46    inference(superposition,[],[f23,f25])).
% 0.18/0.46  fof(f58,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)),k2_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 0.18/0.46    inference(superposition,[],[f24,f25])).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.18/0.46    inference(definition_unfolding,[],[f20,f18,f18,f18])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),
% 0.18/0.46    inference(definition_unfolding,[],[f15,f18])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 0.18/0.46    inference(cnf_transformation,[],[f12])).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (27764)------------------------------
% 0.18/0.46  % (27764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (27764)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (27764)Memory used [KB]: 2046
% 0.18/0.46  % (27764)Time elapsed: 0.049 s
% 0.18/0.46  % (27764)------------------------------
% 0.18/0.46  % (27764)------------------------------
% 0.18/0.46  % (27747)Success in time 0.119 s
%------------------------------------------------------------------------------
