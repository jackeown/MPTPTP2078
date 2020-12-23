%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:41 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 197 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 246 expanded)
%              Number of equality atoms :   62 ( 189 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(subsumption_resolution,[],[f162,f99])).

fof(f99,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f54,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f51,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

% (1263)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f54,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f29,f52,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

% (1284)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f162,plain,(
    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f161,f55])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f31,f52])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f161,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f144,f127])).

fof(f127,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f126,f75])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(resolution,[],[f60,f65])).

fof(f65,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f126,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f120,f66])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f39,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f120,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,k3_xboole_0(X3,X3)) ),
    inference(superposition,[],[f57,f88])).

fof(f88,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f55,f56])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f37,f36,f36,f52])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f144,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f58,f141])).

fof(f141,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f77,f28])).

fof(f28,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3) ) ),
    inference(resolution,[],[f61,f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f38,f52,f36,f52])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:13:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.22/0.56  % (1273)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.22/0.56  % (1258)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.56  % (1262)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.22/0.56  % (1281)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.56  % (1281)Refutation not found, incomplete strategy% (1281)------------------------------
% 1.22/0.56  % (1281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.56  % (1281)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.56  
% 1.22/0.56  % (1281)Memory used [KB]: 6268
% 1.22/0.56  % (1281)Time elapsed: 0.134 s
% 1.22/0.56  % (1281)------------------------------
% 1.22/0.56  % (1281)------------------------------
% 1.53/0.56  % (1273)Refutation not found, incomplete strategy% (1273)------------------------------
% 1.53/0.56  % (1273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (1264)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.53/0.56  % (1273)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (1273)Memory used [KB]: 1663
% 1.53/0.56  % (1273)Time elapsed: 0.132 s
% 1.53/0.56  % (1273)------------------------------
% 1.53/0.56  % (1273)------------------------------
% 1.53/0.57  % (1260)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.57  % (1264)Refutation not found, incomplete strategy% (1264)------------------------------
% 1.53/0.57  % (1264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (1264)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (1264)Memory used [KB]: 10618
% 1.53/0.57  % (1264)Time elapsed: 0.143 s
% 1.53/0.57  % (1264)------------------------------
% 1.53/0.57  % (1264)------------------------------
% 1.53/0.57  % (1260)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % (1274)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.53/0.57  % (1278)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.53/0.58  % (1257)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.53/0.58  % (1277)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.53/0.58  % (1265)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.59  % (1259)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.53/0.59  % (1265)Refutation not found, incomplete strategy% (1265)------------------------------
% 1.53/0.59  % (1265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (1265)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (1265)Memory used [KB]: 6268
% 1.53/0.59  % (1265)Time elapsed: 0.143 s
% 1.53/0.59  % (1265)------------------------------
% 1.53/0.59  % (1265)------------------------------
% 1.53/0.59  % (1254)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.53/0.59  % (1269)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.53/0.60  % (1283)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.53/0.60  % (1268)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.53/0.60  % SZS output start Proof for theBenchmark
% 1.53/0.60  fof(f163,plain,(
% 1.53/0.60    $false),
% 1.53/0.60    inference(subsumption_resolution,[],[f162,f99])).
% 1.53/0.60  fof(f99,plain,(
% 1.53/0.60    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.53/0.60    inference(forward_demodulation,[],[f54,f56])).
% 1.53/0.60  fof(f56,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.53/0.60    inference(definition_unfolding,[],[f33,f51,f51])).
% 1.53/0.60  fof(f51,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.53/0.60    inference(definition_unfolding,[],[f34,f50])).
% 1.53/0.60  fof(f50,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.53/0.60    inference(definition_unfolding,[],[f48,f49])).
% 1.53/0.60  fof(f49,plain,(
% 1.53/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f14])).
% 1.53/0.60  fof(f14,axiom,(
% 1.53/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.53/0.60  fof(f48,plain,(
% 1.53/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f13])).
% 1.53/0.60  fof(f13,axiom,(
% 1.53/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.60  fof(f34,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f12])).
% 1.53/0.60  % (1263)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.53/0.60  fof(f12,axiom,(
% 1.53/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.60  fof(f33,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f10])).
% 1.53/0.60  fof(f10,axiom,(
% 1.53/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.53/0.60  fof(f54,plain,(
% 1.53/0.60    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.53/0.60    inference(definition_unfolding,[],[f29,f52,f53])).
% 1.53/0.60  fof(f53,plain,(
% 1.53/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.53/0.60    inference(definition_unfolding,[],[f32,f51])).
% 1.53/0.60  fof(f32,plain,(
% 1.53/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f11])).
% 1.53/0.60  fof(f11,axiom,(
% 1.53/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.60  fof(f52,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.53/0.60    inference(definition_unfolding,[],[f35,f51])).
% 1.53/0.60  fof(f35,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.53/0.60    inference(cnf_transformation,[],[f16])).
% 1.53/0.60  fof(f16,axiom,(
% 1.53/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.53/0.60  fof(f29,plain,(
% 1.53/0.60    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.53/0.60    inference(cnf_transformation,[],[f23])).
% 1.53/0.60  fof(f23,plain,(
% 1.53/0.60    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.53/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 1.53/0.60  fof(f22,plain,(
% 1.53/0.60    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.53/0.60    introduced(choice_axiom,[])).
% 1.53/0.60  fof(f19,plain,(
% 1.53/0.60    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.53/0.60    inference(ennf_transformation,[],[f18])).
% 1.53/0.60  % (1284)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.53/0.60  fof(f18,negated_conjecture,(
% 1.53/0.60    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.53/0.60    inference(negated_conjecture,[],[f17])).
% 1.53/0.60  fof(f17,conjecture,(
% 1.53/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.53/0.60  fof(f162,plain,(
% 1.53/0.60    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.53/0.60    inference(forward_demodulation,[],[f161,f55])).
% 1.53/0.60  fof(f55,plain,(
% 1.53/0.60    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.53/0.60    inference(definition_unfolding,[],[f31,f52])).
% 1.53/0.60  fof(f31,plain,(
% 1.53/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.60    inference(cnf_transformation,[],[f4])).
% 1.53/0.60  fof(f4,axiom,(
% 1.53/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.53/0.60  fof(f161,plain,(
% 1.53/0.60    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))),
% 1.53/0.60    inference(forward_demodulation,[],[f144,f127])).
% 1.53/0.60  fof(f127,plain,(
% 1.53/0.60    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 1.53/0.60    inference(forward_demodulation,[],[f126,f75])).
% 1.53/0.60  fof(f75,plain,(
% 1.53/0.60    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) )),
% 1.53/0.60    inference(resolution,[],[f60,f65])).
% 1.53/0.60  fof(f65,plain,(
% 1.53/0.60    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.53/0.60    inference(resolution,[],[f40,f30])).
% 1.53/0.60  fof(f30,plain,(
% 1.53/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f8])).
% 1.53/0.60  fof(f8,axiom,(
% 1.53/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.53/0.60  fof(f40,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f21])).
% 1.53/0.60  fof(f21,plain,(
% 1.53/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.53/0.60    inference(ennf_transformation,[],[f1])).
% 1.53/0.60  fof(f1,axiom,(
% 1.53/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.53/0.60  fof(f60,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.53/0.60    inference(definition_unfolding,[],[f44,f36])).
% 1.53/0.60  fof(f36,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.60    inference(cnf_transformation,[],[f3])).
% 1.53/0.60  fof(f3,axiom,(
% 1.53/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.53/0.60  fof(f44,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f26])).
% 1.53/0.60  fof(f26,plain,(
% 1.53/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.53/0.60    inference(nnf_transformation,[],[f9])).
% 1.53/0.60  fof(f9,axiom,(
% 1.53/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.53/0.60  fof(f126,plain,(
% 1.53/0.60    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,X3)) )),
% 1.53/0.60    inference(forward_demodulation,[],[f120,f66])).
% 1.53/0.60  fof(f66,plain,(
% 1.53/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.60    inference(resolution,[],[f39,f63])).
% 1.53/0.60  fof(f63,plain,(
% 1.53/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.53/0.60    inference(equality_resolution,[],[f42])).
% 1.53/0.60  fof(f42,plain,(
% 1.53/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f25,plain,(
% 1.53/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.60    inference(flattening,[],[f24])).
% 1.53/0.60  fof(f24,plain,(
% 1.53/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.60    inference(nnf_transformation,[],[f2])).
% 1.53/0.60  fof(f2,axiom,(
% 1.53/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.60  fof(f39,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.53/0.60    inference(cnf_transformation,[],[f20])).
% 1.53/0.60  fof(f20,plain,(
% 1.53/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.60    inference(ennf_transformation,[],[f5])).
% 1.53/0.60  fof(f5,axiom,(
% 1.53/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.53/0.60  fof(f120,plain,(
% 1.53/0.60    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,k3_xboole_0(X3,X3))) )),
% 1.53/0.60    inference(superposition,[],[f57,f88])).
% 1.53/0.60  fof(f88,plain,(
% 1.53/0.60    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.53/0.60    inference(superposition,[],[f55,f56])).
% 1.53/0.60  fof(f57,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.53/0.60    inference(definition_unfolding,[],[f37,f36,f36,f52])).
% 1.53/0.60  fof(f37,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f7])).
% 1.53/0.60  fof(f7,axiom,(
% 1.53/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.53/0.60  fof(f144,plain,(
% 1.53/0.60    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.53/0.60    inference(superposition,[],[f58,f141])).
% 1.53/0.60  fof(f141,plain,(
% 1.53/0.60    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.53/0.60    inference(resolution,[],[f77,f28])).
% 1.53/0.60  fof(f28,plain,(
% 1.53/0.60    r2_hidden(sK0,sK1)),
% 1.53/0.60    inference(cnf_transformation,[],[f23])).
% 1.53/0.60  fof(f77,plain,(
% 1.53/0.60    ( ! [X2,X3] : (~r2_hidden(X2,X3) | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3)) )),
% 1.53/0.60    inference(resolution,[],[f61,f39])).
% 1.53/0.60  fof(f61,plain,(
% 1.53/0.60    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.60    inference(definition_unfolding,[],[f47,f53])).
% 1.53/0.60  fof(f47,plain,(
% 1.53/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f27])).
% 1.53/0.60  fof(f27,plain,(
% 1.53/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.53/0.60    inference(nnf_transformation,[],[f15])).
% 1.53/0.60  fof(f15,axiom,(
% 1.53/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.53/0.60  fof(f58,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.53/0.60    inference(definition_unfolding,[],[f38,f52,f36,f52])).
% 1.53/0.60  fof(f38,plain,(
% 1.53/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f6])).
% 1.53/0.60  fof(f6,axiom,(
% 1.53/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.53/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.53/0.60  % SZS output end Proof for theBenchmark
% 1.53/0.60  % (1260)------------------------------
% 1.53/0.60  % (1260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (1260)Termination reason: Refutation
% 1.53/0.60  
% 1.53/0.60  % (1260)Memory used [KB]: 10746
% 1.53/0.60  % (1260)Time elapsed: 0.149 s
% 1.53/0.60  % (1260)------------------------------
% 1.53/0.60  % (1260)------------------------------
% 1.53/0.60  % (1253)Success in time 0.235 s
%------------------------------------------------------------------------------
