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
% DateTime   : Thu Dec  3 12:39:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 388 expanded)
%              Number of leaves         :   11 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          :   88 ( 568 expanded)
%              Number of equality atoms :   37 ( 307 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(resolution,[],[f242,f114])).

fof(f114,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f104,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f104,plain,(
    ! [X0] : ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f19,f23,f37])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f36])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f242,plain,(
    ! [X1] : r2_hidden(sK0,X1) ),
    inference(global_subsumption,[],[f17,f240])).

fof(f240,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f49,f216])).

fof(f216,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f172,f59])).

fof(f59,plain,(
    ! [X6] : k5_xboole_0(X6,k4_xboole_0(k1_xboole_0,X6)) = X6 ),
    inference(superposition,[],[f40,f54])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(unit_resulting_resolution,[],[f17,f42])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f20,f23,f23])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f172,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(backward_demodulation,[],[f38,f171])).

fof(f171,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f167,f166])).

fof(f166,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f114,f132,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK3(X0,X1,X2),X1,X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ) ),
    inference(definition_unfolding,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK3(X0,X1,X2),X1,X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f132,plain,(
    ! [X0] : ~ sP4(X0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f117,f117,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f117,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f114,f87])).

fof(f87,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f84,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f84,plain,(
    ! [X11] :
      ( ~ sP4(X11,sK2,k2_enumset1(sK0,sK0,sK0,sK1))
      | r2_hidden(X11,k1_xboole_0) ) ),
    inference(superposition,[],[f51,f38])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f29,f23])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f167,plain,(
    sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f117,f132,f44])).

fof(f38,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f23,f36])).

fof(f16,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (29238)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.48  % (29238)Refutation not found, incomplete strategy% (29238)------------------------------
% 0.21/0.48  % (29238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (29238)Memory used [KB]: 10618
% 0.21/0.48  % (29238)Time elapsed: 0.073 s
% 0.21/0.48  % (29238)------------------------------
% 0.21/0.48  % (29238)------------------------------
% 0.21/0.48  % (29233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (29255)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.48  % (29246)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (29246)Refutation not found, incomplete strategy% (29246)------------------------------
% 0.21/0.49  % (29246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29246)Memory used [KB]: 10618
% 0.21/0.49  % (29246)Time elapsed: 0.076 s
% 0.21/0.49  % (29246)------------------------------
% 0.21/0.49  % (29246)------------------------------
% 0.21/0.49  % (29232)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.49  % (29249)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (29233)Refutation not found, incomplete strategy% (29233)------------------------------
% 0.21/0.49  % (29233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29241)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (29233)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29233)Memory used [KB]: 6140
% 0.21/0.49  % (29233)Time elapsed: 0.077 s
% 0.21/0.49  % (29233)------------------------------
% 0.21/0.49  % (29233)------------------------------
% 0.21/0.49  % (29244)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (29244)Refutation not found, incomplete strategy% (29244)------------------------------
% 0.21/0.49  % (29244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29244)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29244)Memory used [KB]: 6140
% 0.21/0.49  % (29244)Time elapsed: 0.002 s
% 0.21/0.49  % (29244)------------------------------
% 0.21/0.49  % (29244)------------------------------
% 0.21/0.50  % (29249)Refutation not found, incomplete strategy% (29249)------------------------------
% 0.21/0.50  % (29249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29249)Memory used [KB]: 10746
% 0.21/0.50  % (29249)Time elapsed: 0.089 s
% 0.21/0.50  % (29249)------------------------------
% 0.21/0.50  % (29249)------------------------------
% 0.21/0.50  % (29242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (29229)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (29234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (29251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (29236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (29253)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (29230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (29239)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (29239)Refutation not found, incomplete strategy% (29239)------------------------------
% 0.21/0.51  % (29239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29239)Memory used [KB]: 10618
% 0.21/0.51  % (29239)Time elapsed: 0.083 s
% 0.21/0.51  % (29239)------------------------------
% 0.21/0.51  % (29239)------------------------------
% 0.21/0.51  % (29259)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (29252)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (29245)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (29257)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (29231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (29247)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (29235)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (29229)Refutation not found, incomplete strategy% (29229)------------------------------
% 0.21/0.52  % (29229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29250)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (29237)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (29250)Refutation not found, incomplete strategy% (29250)------------------------------
% 0.21/0.52  % (29250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29258)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (29229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29229)Memory used [KB]: 1663
% 0.21/0.52  % (29229)Time elapsed: 0.114 s
% 0.21/0.52  % (29229)------------------------------
% 0.21/0.52  % (29229)------------------------------
% 0.21/0.52  % (29256)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (29243)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (29240)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (29253)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (29250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29250)Memory used [KB]: 1663
% 0.21/0.53  % (29250)Time elapsed: 0.117 s
% 0.21/0.53  % (29250)------------------------------
% 0.21/0.53  % (29250)------------------------------
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f254,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(resolution,[],[f242,f114])).
% 1.25/0.53  fof(f114,plain,(
% 1.25/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.25/0.53    inference(duplicate_literal_removal,[],[f113])).
% 1.25/0.53  fof(f113,plain,(
% 1.25/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.25/0.53    inference(resolution,[],[f104,f47])).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f35,f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f21,f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.25/0.53  fof(f104,plain,(
% 1.25/0.53    ( ! [X0] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_xboole_0)) )),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f39,f42])).
% 1.25/0.53  fof(f42,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f24,f23])).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f5])).
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.25/0.53    inference(cnf_transformation,[],[f15])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f19,f23,f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f18,f36])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.53  fof(f19,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f11])).
% 1.25/0.53  fof(f11,axiom,(
% 1.25/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.25/0.53  fof(f242,plain,(
% 1.25/0.53    ( ! [X1] : (r2_hidden(sK0,X1)) )),
% 1.25/0.53    inference(global_subsumption,[],[f17,f240])).
% 1.25/0.53  fof(f240,plain,(
% 1.25/0.53    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | r2_hidden(sK0,X1)) )),
% 1.25/0.53    inference(superposition,[],[f49,f216])).
% 1.25/0.53  fof(f216,plain,(
% 1.25/0.53    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 1.25/0.53    inference(superposition,[],[f172,f59])).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    ( ! [X6] : (k5_xboole_0(X6,k4_xboole_0(k1_xboole_0,X6)) = X6) )),
% 1.25/0.53    inference(superposition,[],[f40,f54])).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f17,f42])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f20,f23,f23])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.25/0.53  fof(f172,plain,(
% 1.25/0.53    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.25/0.53    inference(backward_demodulation,[],[f38,f171])).
% 1.25/0.53  fof(f171,plain,(
% 1.25/0.53    k1_xboole_0 = sK2),
% 1.25/0.53    inference(backward_demodulation,[],[f167,f166])).
% 1.25/0.53  fof(f166,plain,(
% 1.25/0.53    k1_xboole_0 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2))),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f114,f132,f44])).
% 1.25/0.53  fof(f44,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (sP4(sK3(X0,X1,X2),X1,X0) | r2_hidden(sK3(X0,X1,X2),X2) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2) )),
% 1.25/0.53    inference(definition_unfolding,[],[f31,f23])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (sP4(sK3(X0,X1,X2),X1,X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.25/0.53  fof(f132,plain,(
% 1.25/0.53    ( ! [X0] : (~sP4(X0,sK2,sK2)) )),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f117,f117,f28])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f117,plain,(
% 1.25/0.53    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f114,f87])).
% 1.25/0.53  fof(f87,plain,(
% 1.25/0.53    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,k1_xboole_0)) )),
% 1.25/0.53    inference(resolution,[],[f84,f27])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ( ! [X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f84,plain,(
% 1.25/0.53    ( ! [X11] : (~sP4(X11,sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(X11,k1_xboole_0)) )),
% 1.25/0.53    inference(superposition,[],[f51,f38])).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~sP4(X3,X1,X0)) )),
% 1.25/0.53    inference(equality_resolution,[],[f46])).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 1.25/0.53    inference(definition_unfolding,[],[f29,f23])).
% 1.25/0.53  fof(f29,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f167,plain,(
% 1.25/0.53    sK2 = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2))),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f117,f132,f44])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.25/0.53    inference(definition_unfolding,[],[f16,f23,f36])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.25/0.53    inference(cnf_transformation,[],[f14])).
% 1.25/0.53  fof(f14,plain,(
% 1.25/0.53    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.25/0.53    inference(ennf_transformation,[],[f13])).
% 1.25/0.53  fof(f13,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.25/0.53    inference(negated_conjecture,[],[f12])).
% 1.25/0.53  fof(f12,conjecture,(
% 1.25/0.53    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f33,f36])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (29253)------------------------------
% 1.25/0.53  % (29253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (29253)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (29253)Memory used [KB]: 6396
% 1.25/0.53  % (29253)Time elapsed: 0.104 s
% 1.25/0.53  % (29253)------------------------------
% 1.25/0.53  % (29253)------------------------------
% 1.25/0.53  % (29251)Refutation not found, incomplete strategy% (29251)------------------------------
% 1.25/0.53  % (29251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (29251)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (29251)Memory used [KB]: 10874
% 1.25/0.53  % (29251)Time elapsed: 0.129 s
% 1.25/0.53  % (29251)------------------------------
% 1.25/0.53  % (29251)------------------------------
% 1.25/0.53  % (29228)Success in time 0.163 s
%------------------------------------------------------------------------------
