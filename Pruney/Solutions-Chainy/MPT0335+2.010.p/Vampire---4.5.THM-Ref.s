%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:16 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 148 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 312 expanded)
%              Number of equality atoms :   60 ( 186 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f54,f144])).

fof(f144,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f82,f127])).

fof(f127,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f98,f65])).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f50,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f98,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(superposition,[],[f48,f55])).

fof(f55,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f29,f36,f36,f36,f36])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f82,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f80,f65])).

fof(f80,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(superposition,[],[f49,f73])).

fof(f73,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f72,f25])).

fof(f25,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3,X2)
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X2) ) ),
    inference(resolution,[],[f69,f40])).

fof(f69,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)
      | ~ r2_hidden(sK3,X0) ) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f24,f43,f36])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f36,f36])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f44,f45])).

fof(f44,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f26,f43,f36])).

fof(f26,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:42:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.42  % (19850)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.45  % (19868)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.46  % (19859)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (19847)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (19858)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (19856)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (19864)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (19853)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (19852)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (19848)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (19861)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (19857)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (19857)Refutation not found, incomplete strategy% (19857)------------------------------
% 0.21/0.56  % (19857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19857)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19857)Memory used [KB]: 10746
% 0.21/0.56  % (19857)Time elapsed: 0.148 s
% 0.21/0.56  % (19857)------------------------------
% 0.21/0.56  % (19857)------------------------------
% 1.52/0.57  % (19870)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.52/0.57  % (19867)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.52/0.57  % (19862)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.57  % (19874)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.52/0.57  % (19874)Refutation not found, incomplete strategy% (19874)------------------------------
% 1.52/0.57  % (19874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (19874)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (19874)Memory used [KB]: 6268
% 1.52/0.57  % (19874)Time elapsed: 0.172 s
% 1.52/0.57  % (19874)------------------------------
% 1.52/0.57  % (19874)------------------------------
% 1.52/0.58  % (19849)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.58  % (19851)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.52/0.59  % (19866)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.84/0.59  % (19852)Refutation found. Thanks to Tanya!
% 1.84/0.59  % SZS status Theorem for theBenchmark
% 1.84/0.59  % SZS output start Proof for theBenchmark
% 1.84/0.59  fof(f208,plain,(
% 1.84/0.59    $false),
% 1.84/0.59    inference(trivial_inequality_removal,[],[f201])).
% 1.84/0.59  fof(f201,plain,(
% 1.84/0.59    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.84/0.59    inference(superposition,[],[f54,f144])).
% 1.84/0.59  fof(f144,plain,(
% 1.84/0.59    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.84/0.59    inference(backward_demodulation,[],[f82,f127])).
% 1.84/0.59  fof(f127,plain,(
% 1.84/0.59    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 1.84/0.59    inference(forward_demodulation,[],[f98,f65])).
% 1.84/0.59  fof(f65,plain,(
% 1.84/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.84/0.59    inference(backward_demodulation,[],[f50,f56])).
% 1.84/0.59  fof(f56,plain,(
% 1.84/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.84/0.59    inference(resolution,[],[f40,f52])).
% 1.84/0.59  fof(f52,plain,(
% 1.84/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/0.59    inference(equality_resolution,[],[f31])).
% 1.84/0.59  fof(f31,plain,(
% 1.84/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.84/0.59    inference(cnf_transformation,[],[f21])).
% 1.84/0.59  fof(f21,plain,(
% 1.84/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.59    inference(flattening,[],[f20])).
% 1.84/0.59  fof(f20,plain,(
% 1.84/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.59    inference(nnf_transformation,[],[f3])).
% 1.84/0.59  fof(f3,axiom,(
% 1.84/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.84/0.59  fof(f40,plain,(
% 1.84/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.84/0.59    inference(cnf_transformation,[],[f22])).
% 1.84/0.59  fof(f22,plain,(
% 1.84/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.84/0.59    inference(nnf_transformation,[],[f4])).
% 1.84/0.59  fof(f4,axiom,(
% 1.84/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.84/0.59  fof(f50,plain,(
% 1.84/0.59    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.84/0.59    inference(definition_unfolding,[],[f34,f36])).
% 1.84/0.59  fof(f36,plain,(
% 1.84/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f7])).
% 1.84/0.59  fof(f7,axiom,(
% 1.84/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.84/0.59  fof(f34,plain,(
% 1.84/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.84/0.59    inference(cnf_transformation,[],[f14])).
% 1.84/0.59  fof(f14,plain,(
% 1.84/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.84/0.59    inference(rectify,[],[f2])).
% 1.84/0.59  fof(f2,axiom,(
% 1.84/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.84/0.59  fof(f98,plain,(
% 1.84/0.59    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0))) )),
% 1.84/0.59    inference(superposition,[],[f48,f55])).
% 1.84/0.59  fof(f55,plain,(
% 1.84/0.59    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.84/0.59    inference(resolution,[],[f40,f23])).
% 1.84/0.59  fof(f23,plain,(
% 1.84/0.59    r1_tarski(sK0,sK1)),
% 1.84/0.59    inference(cnf_transformation,[],[f18])).
% 1.84/0.59  fof(f18,plain,(
% 1.84/0.59    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.84/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 1.84/0.59  fof(f17,plain,(
% 1.84/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.84/0.59    introduced(choice_axiom,[])).
% 1.84/0.59  fof(f16,plain,(
% 1.84/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.84/0.59    inference(flattening,[],[f15])).
% 1.84/0.59  fof(f15,plain,(
% 1.84/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.84/0.59    inference(ennf_transformation,[],[f13])).
% 1.84/0.59  fof(f13,negated_conjecture,(
% 1.84/0.59    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.84/0.59    inference(negated_conjecture,[],[f12])).
% 1.84/0.59  fof(f12,conjecture,(
% 1.84/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.84/0.59  fof(f48,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 1.84/0.59    inference(definition_unfolding,[],[f29,f36,f36,f36,f36])).
% 1.84/0.59  fof(f29,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f5])).
% 1.84/0.59  fof(f5,axiom,(
% 1.84/0.59    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.84/0.59  fof(f82,plain,(
% 1.84/0.59    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 1.84/0.59    inference(forward_demodulation,[],[f80,f65])).
% 1.84/0.59  fof(f80,plain,(
% 1.84/0.59    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)),
% 1.84/0.59    inference(superposition,[],[f49,f73])).
% 1.84/0.59  fof(f73,plain,(
% 1.84/0.59    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)),
% 1.84/0.59    inference(resolution,[],[f72,f25])).
% 1.84/0.59  fof(f25,plain,(
% 1.84/0.59    r2_hidden(sK3,sK0)),
% 1.84/0.59    inference(cnf_transformation,[],[f18])).
% 1.84/0.59  fof(f72,plain,(
% 1.84/0.59    ( ! [X2] : (~r2_hidden(sK3,X2) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X2)) )),
% 1.84/0.59    inference(resolution,[],[f69,f40])).
% 1.84/0.59  fof(f69,plain,(
% 1.84/0.59    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) | ~r2_hidden(sK3,X0)) )),
% 1.84/0.59    inference(superposition,[],[f46,f45])).
% 1.84/0.59  fof(f45,plain,(
% 1.84/0.59    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.84/0.59    inference(definition_unfolding,[],[f24,f43,f36])).
% 1.84/0.59  fof(f43,plain,(
% 1.84/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.84/0.59    inference(definition_unfolding,[],[f35,f42])).
% 1.84/0.59  fof(f42,plain,(
% 1.84/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.84/0.59    inference(definition_unfolding,[],[f38,f41])).
% 1.84/0.59  fof(f41,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f10])).
% 1.84/0.59  fof(f10,axiom,(
% 1.84/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.84/0.59  fof(f38,plain,(
% 1.84/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f9])).
% 1.84/0.59  fof(f9,axiom,(
% 1.84/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.84/0.59  fof(f35,plain,(
% 1.84/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f8])).
% 1.84/0.59  fof(f8,axiom,(
% 1.84/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.84/0.59  fof(f24,plain,(
% 1.84/0.59    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 1.84/0.59    inference(cnf_transformation,[],[f18])).
% 1.84/0.59  fof(f46,plain,(
% 1.84/0.59    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.84/0.59    inference(definition_unfolding,[],[f28,f43])).
% 1.84/0.59  fof(f28,plain,(
% 1.84/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f19])).
% 1.84/0.59  fof(f19,plain,(
% 1.84/0.59    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.84/0.59    inference(nnf_transformation,[],[f11])).
% 1.84/0.59  fof(f11,axiom,(
% 1.84/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.84/0.59  fof(f49,plain,(
% 1.84/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.84/0.59    inference(definition_unfolding,[],[f33,f36,f36])).
% 1.84/0.59  fof(f33,plain,(
% 1.84/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f1])).
% 1.84/0.59  fof(f1,axiom,(
% 1.84/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.84/0.59  fof(f54,plain,(
% 1.84/0.59    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.84/0.59    inference(superposition,[],[f44,f45])).
% 1.84/0.59  fof(f44,plain,(
% 1.84/0.59    k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.84/0.59    inference(definition_unfolding,[],[f26,f43,f36])).
% 1.84/0.59  fof(f26,plain,(
% 1.84/0.59    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.84/0.59    inference(cnf_transformation,[],[f18])).
% 1.84/0.59  % SZS output end Proof for theBenchmark
% 1.84/0.59  % (19852)------------------------------
% 1.84/0.59  % (19852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.59  % (19852)Termination reason: Refutation
% 1.84/0.59  
% 1.84/0.59  % (19852)Memory used [KB]: 1918
% 1.84/0.59  % (19852)Time elapsed: 0.177 s
% 1.84/0.59  % (19852)------------------------------
% 1.84/0.59  % (19852)------------------------------
% 1.84/0.59  % (19854)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.84/0.59  % (19871)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.84/0.59  % (19846)Success in time 0.239 s
%------------------------------------------------------------------------------
