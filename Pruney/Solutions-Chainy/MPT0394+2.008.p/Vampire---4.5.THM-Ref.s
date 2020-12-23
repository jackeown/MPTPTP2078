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
% DateTime   : Thu Dec  3 12:45:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 222 expanded)
%              Number of leaves         :   15 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :   82 ( 256 expanded)
%              Number of equality atoms :   65 ( 217 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f789,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f785])).

fof(f785,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f44,f272])).

fof(f272,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(forward_demodulation,[],[f271,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f37,f39,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f271,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) ),
    inference(forward_demodulation,[],[f270,f46])).

fof(f46,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f24,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f270,plain,(
    ! [X0,X1] : k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),X1)) ),
    inference(forward_demodulation,[],[f268,f46])).

fof(f268,plain,(
    ! [X0,X1] : k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k1_setfam_1(k1_enumset1(X1,X1,X1)))) ),
    inference(unit_resulting_resolution,[],[f216,f216,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f39,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f216,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(backward_demodulation,[],[f71,f212])).

fof(f212,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f45,f206])).

fof(f206,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f194,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f194,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f173,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f173,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f158,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f158,plain,(
    ! [X9] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9) ),
    inference(forward_demodulation,[],[f149,f99])).

fof(f99,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f86,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f47,f45])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f29,f29])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f149,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X9) ),
    inference(superposition,[],[f48,f86])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f71,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f51,f32])).

fof(f51,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f35,f40,f40])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f44,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f22,f29,f28])).

fof(f22,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (7318)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (7304)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (7310)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (7312)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (7318)Refutation not found, incomplete strategy% (7318)------------------------------
% 0.21/0.55  % (7318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7318)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7318)Memory used [KB]: 6140
% 0.21/0.55  % (7318)Time elapsed: 0.003 s
% 0.21/0.55  % (7318)------------------------------
% 0.21/0.55  % (7318)------------------------------
% 0.21/0.55  % (7326)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (7326)Refutation not found, incomplete strategy% (7326)------------------------------
% 0.21/0.55  % (7326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7326)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7326)Memory used [KB]: 1663
% 0.21/0.55  % (7326)Time elapsed: 0.126 s
% 0.21/0.55  % (7326)------------------------------
% 0.21/0.55  % (7326)------------------------------
% 0.21/0.55  % (7312)Refutation not found, incomplete strategy% (7312)------------------------------
% 0.21/0.55  % (7312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7320)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (7312)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7327)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (7312)Memory used [KB]: 10618
% 0.21/0.55  % (7312)Time elapsed: 0.124 s
% 0.21/0.55  % (7312)------------------------------
% 0.21/0.55  % (7312)------------------------------
% 0.21/0.55  % (7319)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (7308)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (7329)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (7324)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (7306)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (7313)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (7307)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (7324)Refutation not found, incomplete strategy% (7324)------------------------------
% 0.21/0.56  % (7324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7324)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7324)Memory used [KB]: 1663
% 0.21/0.56  % (7324)Time elapsed: 0.137 s
% 0.21/0.56  % (7324)------------------------------
% 0.21/0.56  % (7324)------------------------------
% 0.21/0.56  % (7307)Refutation not found, incomplete strategy% (7307)------------------------------
% 0.21/0.56  % (7307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7307)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7307)Memory used [KB]: 6140
% 0.21/0.56  % (7307)Time elapsed: 0.128 s
% 0.21/0.56  % (7307)------------------------------
% 0.21/0.56  % (7307)------------------------------
% 0.21/0.56  % (7313)Refutation not found, incomplete strategy% (7313)------------------------------
% 0.21/0.56  % (7313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7321)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (7332)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (7305)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (7329)Refutation not found, incomplete strategy% (7329)------------------------------
% 0.21/0.56  % (7329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7320)Refutation not found, incomplete strategy% (7320)------------------------------
% 0.21/0.56  % (7320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7320)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7320)Memory used [KB]: 10618
% 0.21/0.56  % (7320)Time elapsed: 0.129 s
% 0.21/0.56  % (7320)------------------------------
% 0.21/0.56  % (7320)------------------------------
% 0.21/0.56  % (7328)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (7305)Refutation not found, incomplete strategy% (7305)------------------------------
% 0.21/0.56  % (7305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7313)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7313)Memory used [KB]: 10618
% 0.21/0.56  % (7329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  % (7313)Time elapsed: 0.092 s
% 0.21/0.56  
% 0.21/0.56  % (7313)------------------------------
% 0.21/0.56  % (7313)------------------------------
% 0.21/0.56  % (7329)Memory used [KB]: 10618
% 0.21/0.56  % (7323)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (7329)Time elapsed: 0.091 s
% 0.21/0.56  % (7329)------------------------------
% 0.21/0.56  % (7329)------------------------------
% 0.21/0.56  % (7311)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (7323)Refutation not found, incomplete strategy% (7323)------------------------------
% 0.21/0.56  % (7323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7323)Memory used [KB]: 10618
% 0.21/0.56  % (7323)Time elapsed: 0.137 s
% 0.21/0.56  % (7323)------------------------------
% 0.21/0.56  % (7323)------------------------------
% 0.21/0.56  % (7305)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7305)Memory used [KB]: 10618
% 0.21/0.56  % (7305)Time elapsed: 0.097 s
% 0.21/0.56  % (7305)------------------------------
% 0.21/0.56  % (7305)------------------------------
% 0.21/0.56  % (7311)Refutation not found, incomplete strategy% (7311)------------------------------
% 0.21/0.56  % (7311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7311)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7311)Memory used [KB]: 10618
% 0.21/0.56  % (7311)Time elapsed: 0.134 s
% 0.21/0.56  % (7311)------------------------------
% 0.21/0.56  % (7311)------------------------------
% 0.21/0.57  % (7322)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (7325)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (7316)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (7325)Refutation not found, incomplete strategy% (7325)------------------------------
% 0.21/0.57  % (7325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7325)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7325)Memory used [KB]: 10618
% 0.21/0.57  % (7325)Time elapsed: 0.146 s
% 0.21/0.57  % (7325)------------------------------
% 0.21/0.57  % (7325)------------------------------
% 0.21/0.57  % (7317)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (7331)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (7303)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (7303)Refutation not found, incomplete strategy% (7303)------------------------------
% 0.21/0.57  % (7303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7303)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7303)Memory used [KB]: 1663
% 0.21/0.57  % (7303)Time elapsed: 0.136 s
% 0.21/0.57  % (7303)------------------------------
% 0.21/0.57  % (7303)------------------------------
% 0.21/0.57  % (7309)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (7330)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (7315)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (7314)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (7314)Refutation not found, incomplete strategy% (7314)------------------------------
% 0.21/0.58  % (7314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (7314)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (7314)Memory used [KB]: 10618
% 0.21/0.58  % (7314)Time elapsed: 0.150 s
% 0.21/0.58  % (7314)------------------------------
% 0.21/0.58  % (7314)------------------------------
% 0.21/0.58  % (7327)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f789,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f785])).
% 0.21/0.58  fof(f785,plain,(
% 0.21/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.58    inference(superposition,[],[f44,f272])).
% 0.21/0.58  fof(f272,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f271,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f36,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f37,f39,f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f25,f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f27,f28])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.58  fof(f271,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f270,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f24,f40])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.58  fof(f270,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),X1))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f268,f46])).
% 0.21/0.58  fof(f268,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k1_setfam_1(k1_enumset1(X1,X1,X1))))) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f216,f216,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f34,f39,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.21/0.58  fof(f216,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.21/0.58    inference(backward_demodulation,[],[f71,f212])).
% 0.21/0.58  fof(f212,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.58    inference(backward_demodulation,[],[f45,f206])).
% 0.21/0.58  fof(f206,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f194,f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.58  fof(f194,plain,(
% 0.21/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f173,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.58  fof(f173,plain,(
% 0.21/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f158,f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f158,plain,(
% 0.21/0.58    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f149,f99])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.58    inference(superposition,[],[f86,f86])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.58    inference(superposition,[],[f47,f45])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f26,f29,f29])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.58  fof(f149,plain,(
% 0.21/0.58    ( ! [X9] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X9)) )),
% 0.21/0.58    inference(superposition,[],[f48,f86])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f30,f29])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f23,f29])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ( ! [X0] : (k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f51,f32])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.21/0.58    inference(equality_resolution,[],[f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 != X1) )),
% 0.21/0.58    inference(definition_unfolding,[],[f35,f40,f40])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.21/0.58    inference(definition_unfolding,[],[f22,f29,f28])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.58    inference(negated_conjecture,[],[f16])).
% 0.21/0.58  fof(f16,conjecture,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (7327)------------------------------
% 0.21/0.58  % (7327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (7327)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (7327)Memory used [KB]: 6524
% 0.21/0.58  % (7327)Time elapsed: 0.156 s
% 0.21/0.58  % (7327)------------------------------
% 0.21/0.58  % (7327)------------------------------
% 0.21/0.58  % (7328)Refutation not found, incomplete strategy% (7328)------------------------------
% 0.21/0.58  % (7328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (7328)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (7328)Memory used [KB]: 6140
% 0.21/0.58  % (7328)Time elapsed: 0.127 s
% 0.21/0.58  % (7328)------------------------------
% 0.21/0.58  % (7328)------------------------------
% 0.21/0.59  % (7301)Success in time 0.206 s
%------------------------------------------------------------------------------
