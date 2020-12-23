%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 389 expanded)
%              Number of leaves         :   12 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :   73 ( 484 expanded)
%              Number of equality atoms :   72 ( 483 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f75])).

fof(f75,plain,(
    ! [X0] : sK0 = X0 ),
    inference(global_subsumption,[],[f51,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | sK0 = X0
      | sK0 = X0 ) ),
    inference(superposition,[],[f62,f63])).

fof(f63,plain,(
    ! [X1] :
      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)))
      | sK0 = X1 ) ),
    inference(superposition,[],[f36,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_xboole_0))
      | sK0 = X0 ) ),
    inference(superposition,[],[f38,f45])).

fof(f45,plain,(
    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(global_subsumption,[],[f19,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f35,f38])).

fof(f35,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f18,f26,f34,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f18,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f28,f34,f26,f34,f34])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

% (20173)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0))))
      | sK0 = X0 ) ),
    inference(superposition,[],[f37,f49])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f23,f26,f31])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f51,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f48,f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f48,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f40,f45])).

fof(f40,plain,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) != k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k3_enumset1(X0,X0,X0,X0,X0) != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f27,f34,f26,f34,f34])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.54  % (20186)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (20169)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (20163)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (20162)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (20164)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (20179)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (20164)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (20176)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (20185)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (20162)Refutation not found, incomplete strategy% (20162)------------------------------
% 0.21/0.56  % (20162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20162)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20162)Memory used [KB]: 1663
% 0.21/0.56  % (20162)Time elapsed: 0.148 s
% 0.21/0.56  % (20162)------------------------------
% 0.21/0.56  % (20162)------------------------------
% 0.21/0.56  % (20165)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (20178)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (20168)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (20167)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (20172)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (20183)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (20172)Refutation not found, incomplete strategy% (20172)------------------------------
% 0.21/0.57  % (20172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20172)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20172)Memory used [KB]: 10618
% 0.21/0.57  % (20172)Time elapsed: 0.156 s
% 0.21/0.57  % (20172)------------------------------
% 0.21/0.57  % (20172)------------------------------
% 0.21/0.57  % (20188)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (20191)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f19,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X0] : (sK0 = X0) )),
% 0.21/0.57    inference(global_subsumption,[],[f51,f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | sK0 = X0) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | sK0 = X0 | sK0 = X0) )),
% 0.21/0.57    inference(superposition,[],[f62,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1))) | sK0 = X1) )),
% 0.21/0.57    inference(superposition,[],[f36,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_xboole_0)) | sK0 = X0) )),
% 0.21/0.57    inference(superposition,[],[f38,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.57    inference(global_subsumption,[],[f19,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK1),
% 0.21/0.57    inference(superposition,[],[f35,f38])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.21/0.57    inference(definition_unfolding,[],[f18,f26,f34,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f20,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f24,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f29,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.57    inference(negated_conjecture,[],[f11])).
% 0.21/0.57  fof(f11,conjecture,(
% 0.21/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) | X0 = X1) )),
% 0.21/0.57    inference(definition_unfolding,[],[f28,f34,f26,f34,f34])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f22,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f25,f26])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  % (20173)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0)))) | sK0 = X0) )),
% 0.21/0.57    inference(superposition,[],[f37,f49])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f23,f26,f31])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f48,f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.57    inference(rectify,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.21/0.57    inference(superposition,[],[f40,f45])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X1] : (k3_enumset1(X1,X1,X1,X1,X1) != k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)))) )),
% 0.21/0.57    inference(equality_resolution,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (X0 != X1 | k3_enumset1(X0,X0,X0,X0,X0) != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f27,f34,f26,f34,f34])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    sK0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (20164)------------------------------
% 0.21/0.57  % (20164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20164)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (20164)Memory used [KB]: 10746
% 0.21/0.57  % (20164)Time elapsed: 0.132 s
% 0.21/0.57  % (20164)------------------------------
% 0.21/0.57  % (20164)------------------------------
% 0.21/0.57  % (20161)Success in time 0.211 s
%------------------------------------------------------------------------------
