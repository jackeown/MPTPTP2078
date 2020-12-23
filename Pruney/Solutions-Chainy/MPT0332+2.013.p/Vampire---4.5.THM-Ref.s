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
% DateTime   : Thu Dec  3 12:43:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 464 expanded)
%              Number of leaves         :   14 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :   97 ( 613 expanded)
%              Number of equality atoms :   65 ( 416 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f714,plain,(
    $false ),
    inference(subsumption_resolution,[],[f680,f111])).

fof(f111,plain,(
    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(resolution,[],[f91,f20])).

fof(f20,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f91,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | sK2 = k4_xboole_0(sK2,k2_enumset1(X1,X1,X1,sK1)) ) ),
    inference(resolution,[],[f42,f21])).

fof(f21,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f680,plain,(
    sK2 != k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f120,f553])).

fof(f553,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f552,f173])).

fof(f173,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f164,f65])).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f61,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f38,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f25,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f39,f44])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f27,f30,f30])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f164,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f163,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f43,f45])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(backward_demodulation,[],[f37,f38])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f163,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f162,f45])).

fof(f162,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f161,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f51,f25])).

fof(f51,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(superposition,[],[f29,f46])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f161,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f146,f45])).

fof(f146,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0))) = X0 ),
    inference(superposition,[],[f40,f44])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0))) = X0 ),
    inference(definition_unfolding,[],[f28,f35,f30])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f552,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f529,f164])).

fof(f529,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),X2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f422,f498])).

fof(f498,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f478,f39])).

fof(f478,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f457,f45])).

fof(f457,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f456,f44])).

fof(f456,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f407,f46])).

fof(f407,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X0),X1) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[],[f41,f52])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) ),
    inference(definition_unfolding,[],[f33,f30,f30,f30])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f422,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3))),k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3))))) ),
    inference(forward_demodulation,[],[f374,f45])).

fof(f374,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3))),k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X2,k1_xboole_0)),k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3))))) ),
    inference(superposition,[],[f41,f52])).

fof(f120,plain,(
    sK2 != k4_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(backward_demodulation,[],[f36,f115])).

fof(f115,plain,(
    k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[],[f39,f111])).

fof(f36,plain,(
    sK2 != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f22,f30,f31,f31])).

fof(f22,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (14675)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.42  % (14674)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.42  % (14673)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.43  % (14672)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.43  % (14668)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (14678)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.44  % (14677)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.44  % (14676)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.44  % (14669)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (14666)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.44  % (14671)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (14664)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.45  % (14665)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.45  % (14673)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f714,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f680,f111])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.45    inference(resolution,[],[f91,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.45    inference(negated_conjecture,[],[f13])).
% 0.21/0.45  fof(f13,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ( ! [X1] : (r2_hidden(X1,sK2) | sK2 = k4_xboole_0(sK2,k2_enumset1(X1,X1,X1,sK1))) )),
% 0.21/0.45    inference(resolution,[],[f42,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ~r2_hidden(sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 0.21/0.45    inference(definition_unfolding,[],[f34,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.21/0.45  fof(f680,plain,(
% 0.21/0.45    sK2 != k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.45    inference(superposition,[],[f120,f553])).
% 0.21/0.45  fof(f553,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X2,X3),X2)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f552,f173])).
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(superposition,[],[f164,f65])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.45    inference(forward_demodulation,[],[f61,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(backward_demodulation,[],[f38,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.45    inference(resolution,[],[f25,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f24,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.45    inference(superposition,[],[f39,f44])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f27,f30,f30])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.45    inference(forward_demodulation,[],[f163,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.45    inference(backward_demodulation,[],[f43,f45])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 0.21/0.45    inference(backward_demodulation,[],[f37,f38])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f23,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f32,f30])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.45  fof(f163,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 0.21/0.45    inference(forward_demodulation,[],[f162,f45])).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.45    inference(forward_demodulation,[],[f161,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.45    inference(resolution,[],[f51,f25])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 0.21/0.45    inference(superposition,[],[f29,f46])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 0.21/0.45  fof(f161,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0) )),
% 0.21/0.45    inference(forward_demodulation,[],[f146,f45])).
% 0.21/0.45  fof(f146,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0))) = X0) )),
% 0.21/0.45    inference(superposition,[],[f40,f44])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0))) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f28,f35,f30])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.45  fof(f552,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f529,f164])).
% 0.21/0.45  fof(f529,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),X2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0))) )),
% 0.21/0.45    inference(backward_demodulation,[],[f422,f498])).
% 0.21/0.45  fof(f498,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 0.21/0.45    inference(superposition,[],[f478,f39])).
% 0.21/0.45  fof(f478,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k5_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 0.21/0.46    inference(superposition,[],[f457,f45])).
% 0.21/0.46  fof(f457,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f456,f44])).
% 0.21/0.46  fof(f456,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f407,f46])).
% 0.21/0.46  fof(f407,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X0),X1) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0)) )),
% 0.21/0.46    inference(superposition,[],[f41,f52])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f33,f30,f30,f30])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).
% 0.21/0.46  fof(f422,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3))),k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f374,f45])).
% 0.21/0.46  fof(f374,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3))),k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X2,k1_xboole_0)),k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,X3)))))) )),
% 0.21/0.46    inference(superposition,[],[f41,f52])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    sK2 != k4_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.46    inference(backward_demodulation,[],[f36,f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.46    inference(superposition,[],[f39,f111])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    sK2 != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.46    inference(definition_unfolding,[],[f22,f30,f31,f31])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (14673)------------------------------
% 0.21/0.46  % (14673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (14673)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (14673)Memory used [KB]: 11385
% 0.21/0.46  % (14673)Time elapsed: 0.040 s
% 0.21/0.46  % (14673)------------------------------
% 0.21/0.46  % (14673)------------------------------
% 0.21/0.46  % (14681)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (14663)Success in time 0.1 s
%------------------------------------------------------------------------------
