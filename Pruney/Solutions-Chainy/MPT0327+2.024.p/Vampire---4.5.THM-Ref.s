%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:51 EST 2020

% Result     : Theorem 10.35s
% Output     : Refutation 10.35s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 159 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 181 expanded)
%              Number of equality atoms :   39 ( 145 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14354,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f14353])).

fof(f14353,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f14317,f92])).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f54,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f56,f54])).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f14317,plain,(
    sK1 != k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f691,f14254])).

fof(f14254,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f86,f603])).

fof(f603,plain,(
    ! [X8] :
      ( ~ r1_xboole_0(X8,X8)
      | k1_xboole_0 = X8 ) ),
    inference(forward_demodulation,[],[f602,f88])).

fof(f602,plain,(
    ! [X8] :
      ( k4_xboole_0(X8,X8) = X8
      | ~ r1_xboole_0(X8,X8) ) ),
    inference(forward_demodulation,[],[f575,f92])).

fof(f575,plain,(
    ! [X8] :
      ( k4_xboole_0(k5_xboole_0(X8,k1_xboole_0),X8) = X8
      | ~ r1_xboole_0(X8,X8) ) ),
    inference(superposition,[],[f58,f88])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),X0),k4_xboole_0(X1,sK1)) ),
    inference(unit_resulting_resolution,[],[f78,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f78,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_tarski(sK0,sK0),X0),sK1) ),
    inference(unit_resulting_resolution,[],[f74,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f74,plain,(
    r1_tarski(k2_tarski(sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f25,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f27])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f691,plain,(
    sK1 != k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),sK1)) ),
    inference(superposition,[],[f605,f55])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f29,f31,f31])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f605,plain,(
    sK1 != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(backward_demodulation,[],[f202,f604])).

fof(f604,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k4_xboole_0(k4_xboole_0(X10,X9),X9) ),
    inference(forward_demodulation,[],[f576,f92])).

fof(f576,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X10,X9),X9) = k4_xboole_0(X10,k5_xboole_0(X9,k1_xboole_0)) ),
    inference(superposition,[],[f61,f88])).

fof(f61,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f40,f31])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f202,plain,(
    sK1 != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f53,f55])).

fof(f53,plain,(
    sK1 != k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f26,f31,f27,f27])).

fof(f26,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:08 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.51  % (15042)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (15034)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (15026)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (15022)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (15030)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (15025)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (15024)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (15023)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (15023)Refutation not found, incomplete strategy% (15023)------------------------------
% 0.20/0.53  % (15023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15023)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15023)Memory used [KB]: 10746
% 0.20/0.53  % (15023)Time elapsed: 0.125 s
% 0.20/0.53  % (15023)------------------------------
% 0.20/0.53  % (15023)------------------------------
% 0.20/0.53  % (15032)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (15027)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (15048)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (15050)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (15037)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (15041)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (15039)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (15038)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (15028)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (15047)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (15040)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (15033)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (15049)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (15031)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (15036)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (15029)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (15044)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.56  % (15029)Refutation not found, incomplete strategy% (15029)------------------------------
% 1.56/0.56  % (15029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (15029)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (15029)Memory used [KB]: 10746
% 1.56/0.56  % (15029)Time elapsed: 0.147 s
% 1.56/0.56  % (15029)------------------------------
% 1.56/0.56  % (15029)------------------------------
% 1.56/0.56  % (15021)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.57  % (15046)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.56/0.57  % (15043)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.57  % (15035)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.68/0.58  % (15045)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.68/0.59  % (15043)Refutation not found, incomplete strategy% (15043)------------------------------
% 1.68/0.59  % (15043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (15043)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (15043)Memory used [KB]: 10746
% 1.68/0.59  % (15043)Time elapsed: 0.186 s
% 1.68/0.59  % (15043)------------------------------
% 1.68/0.59  % (15043)------------------------------
% 2.19/0.71  % (15051)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.75/0.74  % (15053)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.75/0.74  % (15054)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.70/0.86  % (15026)Time limit reached!
% 3.70/0.86  % (15026)------------------------------
% 3.70/0.86  % (15026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.86  % (15026)Termination reason: Time limit
% 3.70/0.86  % (15026)Termination phase: Saturation
% 3.70/0.86  
% 3.70/0.86  % (15026)Memory used [KB]: 10234
% 3.70/0.86  % (15026)Time elapsed: 0.400 s
% 3.70/0.86  % (15026)------------------------------
% 3.70/0.86  % (15026)------------------------------
% 3.89/0.91  % (15022)Time limit reached!
% 3.89/0.91  % (15022)------------------------------
% 3.89/0.91  % (15022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.91  % (15022)Termination reason: Time limit
% 3.89/0.91  
% 3.89/0.91  % (15022)Memory used [KB]: 7675
% 3.89/0.91  % (15022)Time elapsed: 0.504 s
% 3.89/0.91  % (15022)------------------------------
% 3.89/0.91  % (15022)------------------------------
% 4.24/0.93  % (15033)Time limit reached!
% 4.24/0.93  % (15033)------------------------------
% 4.24/0.93  % (15033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.93  % (15031)Time limit reached!
% 4.24/0.93  % (15031)------------------------------
% 4.24/0.93  % (15031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.93  % (15038)Time limit reached!
% 4.24/0.93  % (15038)------------------------------
% 4.24/0.93  % (15038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.93  % (15038)Termination reason: Time limit
% 4.24/0.93  
% 4.24/0.93  % (15038)Memory used [KB]: 13048
% 4.24/0.93  % (15038)Time elapsed: 0.507 s
% 4.24/0.93  % (15038)------------------------------
% 4.24/0.93  % (15038)------------------------------
% 4.24/0.93  % (15033)Termination reason: Time limit
% 4.24/0.93  
% 4.24/0.93  % (15033)Memory used [KB]: 10234
% 4.24/0.93  % (15033)Time elapsed: 0.521 s
% 4.24/0.93  % (15033)------------------------------
% 4.24/0.93  % (15033)------------------------------
% 4.24/0.93  % (15031)Termination reason: Time limit
% 4.24/0.93  
% 4.24/0.93  % (15031)Memory used [KB]: 15735
% 4.24/0.93  % (15031)Time elapsed: 0.518 s
% 4.24/0.93  % (15031)------------------------------
% 4.24/0.93  % (15031)------------------------------
% 4.24/0.93  % (15021)Time limit reached!
% 4.24/0.93  % (15021)------------------------------
% 4.24/0.93  % (15021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.93  % (15021)Termination reason: Time limit
% 4.24/0.93  
% 4.24/0.93  % (15021)Memory used [KB]: 4605
% 4.24/0.93  % (15021)Time elapsed: 0.525 s
% 4.24/0.93  % (15021)------------------------------
% 4.24/0.93  % (15021)------------------------------
% 4.43/1.01  % (15055)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.43/1.01  % (15028)Time limit reached!
% 4.43/1.01  % (15028)------------------------------
% 4.43/1.01  % (15028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/1.01  % (15028)Termination reason: Time limit
% 4.43/1.01  
% 4.43/1.01  % (15028)Memory used [KB]: 9594
% 4.43/1.01  % (15028)Time elapsed: 0.607 s
% 4.43/1.01  % (15028)------------------------------
% 4.43/1.01  % (15028)------------------------------
% 4.87/1.02  % (15049)Time limit reached!
% 4.87/1.02  % (15049)------------------------------
% 4.87/1.02  % (15049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.02  % (15049)Termination reason: Time limit
% 4.87/1.02  % (15049)Termination phase: Saturation
% 4.87/1.02  
% 4.87/1.02  % (15049)Memory used [KB]: 9338
% 4.87/1.02  % (15049)Time elapsed: 0.600 s
% 4.87/1.02  % (15049)------------------------------
% 4.87/1.02  % (15049)------------------------------
% 4.87/1.03  % (15037)Time limit reached!
% 4.87/1.03  % (15037)------------------------------
% 4.87/1.03  % (15037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.03  % (15037)Termination reason: Time limit
% 4.87/1.03  
% 4.87/1.03  % (15037)Memory used [KB]: 15863
% 4.87/1.03  % (15037)Time elapsed: 0.618 s
% 4.87/1.03  % (15037)------------------------------
% 4.87/1.03  % (15037)------------------------------
% 4.87/1.04  % (15058)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.87/1.05  % (15056)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.87/1.06  % (15057)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.87/1.07  % (15059)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.63/1.08  % (15060)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.63/1.15  % (15061)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.26/1.16  % (15063)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.26/1.17  % (15062)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.87/1.28  % (15042)Time limit reached!
% 6.87/1.28  % (15042)------------------------------
% 6.87/1.28  % (15042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.87/1.28  % (15042)Termination reason: Time limit
% 6.87/1.28  
% 6.87/1.28  % (15042)Memory used [KB]: 5500
% 6.87/1.28  % (15042)Time elapsed: 0.821 s
% 6.87/1.28  % (15042)------------------------------
% 6.87/1.28  % (15042)------------------------------
% 6.87/1.30  % (15055)Time limit reached!
% 6.87/1.30  % (15055)------------------------------
% 6.87/1.30  % (15055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.42/1.32  % (15055)Termination reason: Time limit
% 7.42/1.32  
% 7.42/1.32  % (15055)Memory used [KB]: 7419
% 7.42/1.32  % (15055)Time elapsed: 0.406 s
% 7.42/1.32  % (15055)------------------------------
% 7.42/1.32  % (15055)------------------------------
% 7.42/1.36  % (15056)Time limit reached!
% 7.42/1.36  % (15056)------------------------------
% 7.42/1.36  % (15056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.42/1.36  % (15056)Termination reason: Time limit
% 7.42/1.36  
% 7.42/1.36  % (15056)Memory used [KB]: 13432
% 7.42/1.36  % (15056)Time elapsed: 0.420 s
% 7.42/1.36  % (15056)------------------------------
% 7.42/1.36  % (15056)------------------------------
% 7.91/1.45  % (15065)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 7.91/1.46  % (15065)Refutation not found, incomplete strategy% (15065)------------------------------
% 7.91/1.46  % (15065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.46  % (15065)Termination reason: Refutation not found, incomplete strategy
% 7.91/1.46  
% 7.91/1.46  % (15065)Memory used [KB]: 1663
% 7.91/1.46  % (15065)Time elapsed: 0.072 s
% 7.91/1.46  % (15065)------------------------------
% 7.91/1.46  % (15065)------------------------------
% 8.57/1.46  % (15064)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.14/1.54  % (15066)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.87/1.63  % (15047)Time limit reached!
% 9.87/1.63  % (15047)------------------------------
% 9.87/1.63  % (15047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.87/1.64  % (15047)Termination reason: Time limit
% 9.87/1.64  
% 9.87/1.64  % (15047)Memory used [KB]: 16630
% 9.87/1.64  % (15047)Time elapsed: 1.210 s
% 9.87/1.64  % (15047)------------------------------
% 9.87/1.64  % (15047)------------------------------
% 9.87/1.65  % (15067)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 10.35/1.71  % (15045)Refutation found. Thanks to Tanya!
% 10.35/1.71  % SZS status Theorem for theBenchmark
% 10.35/1.71  % SZS output start Proof for theBenchmark
% 10.35/1.71  fof(f14354,plain,(
% 10.35/1.71    $false),
% 10.35/1.71    inference(trivial_inequality_removal,[],[f14353])).
% 10.35/1.71  fof(f14353,plain,(
% 10.35/1.71    sK1 != sK1),
% 10.35/1.71    inference(superposition,[],[f14317,f92])).
% 10.35/1.71  fof(f92,plain,(
% 10.35/1.71    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.35/1.71    inference(backward_demodulation,[],[f54,f88])).
% 10.35/1.71  fof(f88,plain,(
% 10.35/1.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 10.35/1.71    inference(superposition,[],[f56,f54])).
% 10.35/1.71  fof(f56,plain,(
% 10.35/1.71    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 10.35/1.71    inference(definition_unfolding,[],[f30,f31])).
% 10.35/1.71  fof(f31,plain,(
% 10.35/1.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 10.35/1.71    inference(cnf_transformation,[],[f11])).
% 10.35/1.71  fof(f11,axiom,(
% 10.35/1.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 10.35/1.71  fof(f30,plain,(
% 10.35/1.71    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 10.35/1.71    inference(cnf_transformation,[],[f8])).
% 10.35/1.71  fof(f8,axiom,(
% 10.35/1.71    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 10.35/1.71  fof(f54,plain,(
% 10.35/1.71    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 10.35/1.71    inference(definition_unfolding,[],[f28,f31])).
% 10.35/1.71  fof(f28,plain,(
% 10.35/1.71    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 10.35/1.71    inference(cnf_transformation,[],[f18])).
% 10.35/1.71  fof(f18,plain,(
% 10.35/1.71    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 10.35/1.71    inference(rectify,[],[f3])).
% 10.35/1.71  fof(f3,axiom,(
% 10.35/1.71    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 10.35/1.71  fof(f14317,plain,(
% 10.35/1.71    sK1 != k5_xboole_0(sK1,k1_xboole_0)),
% 10.35/1.71    inference(backward_demodulation,[],[f691,f14254])).
% 10.35/1.71  fof(f14254,plain,(
% 10.35/1.71    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1)),
% 10.35/1.71    inference(unit_resulting_resolution,[],[f86,f603])).
% 10.35/1.71  fof(f603,plain,(
% 10.35/1.71    ( ! [X8] : (~r1_xboole_0(X8,X8) | k1_xboole_0 = X8) )),
% 10.35/1.71    inference(forward_demodulation,[],[f602,f88])).
% 10.35/1.71  fof(f602,plain,(
% 10.35/1.71    ( ! [X8] : (k4_xboole_0(X8,X8) = X8 | ~r1_xboole_0(X8,X8)) )),
% 10.35/1.71    inference(forward_demodulation,[],[f575,f92])).
% 10.35/1.71  fof(f575,plain,(
% 10.35/1.71    ( ! [X8] : (k4_xboole_0(k5_xboole_0(X8,k1_xboole_0),X8) = X8 | ~r1_xboole_0(X8,X8)) )),
% 10.35/1.71    inference(superposition,[],[f58,f88])).
% 10.35/1.71  fof(f58,plain,(
% 10.35/1.71    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 10.35/1.71    inference(definition_unfolding,[],[f33,f31])).
% 10.35/1.71  fof(f33,plain,(
% 10.35/1.71    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 10.35/1.71    inference(cnf_transformation,[],[f20])).
% 10.35/1.71  fof(f20,plain,(
% 10.35/1.71    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 10.35/1.71    inference(ennf_transformation,[],[f10])).
% 10.35/1.71  fof(f10,axiom,(
% 10.35/1.71    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 10.35/1.71  fof(f86,plain,(
% 10.35/1.71    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),X0),k4_xboole_0(X1,sK1))) )),
% 10.35/1.71    inference(unit_resulting_resolution,[],[f78,f41])).
% 10.35/1.71  fof(f41,plain,(
% 10.35/1.71    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 10.35/1.71    inference(cnf_transformation,[],[f23])).
% 10.35/1.71  fof(f23,plain,(
% 10.35/1.71    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 10.35/1.71    inference(ennf_transformation,[],[f9])).
% 10.35/1.71  fof(f9,axiom,(
% 10.35/1.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 10.35/1.71  fof(f78,plain,(
% 10.35/1.71    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_tarski(sK0,sK0),X0),sK1)) )),
% 10.35/1.71    inference(unit_resulting_resolution,[],[f74,f42])).
% 10.35/1.71  fof(f42,plain,(
% 10.35/1.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 10.35/1.71    inference(cnf_transformation,[],[f24])).
% 10.35/1.71  fof(f24,plain,(
% 10.35/1.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 10.35/1.71    inference(ennf_transformation,[],[f5])).
% 10.35/1.71  fof(f5,axiom,(
% 10.35/1.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 10.35/1.71  fof(f74,plain,(
% 10.35/1.71    r1_tarski(k2_tarski(sK0,sK0),sK1)),
% 10.35/1.71    inference(unit_resulting_resolution,[],[f25,f60])).
% 10.35/1.71  fof(f60,plain,(
% 10.35/1.71    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 10.35/1.71    inference(definition_unfolding,[],[f36,f27])).
% 10.35/1.71  fof(f27,plain,(
% 10.35/1.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 10.35/1.71    inference(cnf_transformation,[],[f12])).
% 10.35/1.71  fof(f12,axiom,(
% 10.35/1.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 10.35/1.71  fof(f36,plain,(
% 10.35/1.71    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 10.35/1.71    inference(cnf_transformation,[],[f13])).
% 10.35/1.71  fof(f13,axiom,(
% 10.35/1.71    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 10.35/1.71  fof(f25,plain,(
% 10.35/1.71    r2_hidden(sK0,sK1)),
% 10.35/1.71    inference(cnf_transformation,[],[f19])).
% 10.35/1.71  fof(f19,plain,(
% 10.35/1.71    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 10.35/1.71    inference(ennf_transformation,[],[f17])).
% 10.35/1.71  fof(f17,negated_conjecture,(
% 10.35/1.71    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 10.35/1.71    inference(negated_conjecture,[],[f16])).
% 10.35/1.71  fof(f16,conjecture,(
% 10.35/1.71    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 10.35/1.71  fof(f691,plain,(
% 10.35/1.71    sK1 != k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),sK1))),
% 10.35/1.71    inference(superposition,[],[f605,f55])).
% 10.35/1.71  fof(f55,plain,(
% 10.35/1.71    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 10.35/1.71    inference(definition_unfolding,[],[f29,f31,f31])).
% 10.35/1.71  fof(f29,plain,(
% 10.35/1.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 10.35/1.71    inference(cnf_transformation,[],[f1])).
% 10.35/1.71  fof(f1,axiom,(
% 10.35/1.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 10.35/1.71  fof(f605,plain,(
% 10.35/1.71    sK1 != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 10.35/1.71    inference(backward_demodulation,[],[f202,f604])).
% 10.35/1.71  fof(f604,plain,(
% 10.35/1.71    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k4_xboole_0(k4_xboole_0(X10,X9),X9)) )),
% 10.35/1.71    inference(forward_demodulation,[],[f576,f92])).
% 10.35/1.71  fof(f576,plain,(
% 10.35/1.71    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X10,X9),X9) = k4_xboole_0(X10,k5_xboole_0(X9,k1_xboole_0))) )),
% 10.35/1.71    inference(superposition,[],[f61,f88])).
% 10.35/1.71  fof(f61,plain,(
% 10.35/1.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 10.35/1.71    inference(definition_unfolding,[],[f40,f31])).
% 10.35/1.71  fof(f40,plain,(
% 10.35/1.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 10.35/1.71    inference(cnf_transformation,[],[f7])).
% 10.35/1.71  fof(f7,axiom,(
% 10.35/1.71    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 10.35/1.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 10.35/1.71  fof(f202,plain,(
% 10.35/1.71    sK1 != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))),
% 10.35/1.71    inference(superposition,[],[f53,f55])).
% 10.35/1.71  fof(f53,plain,(
% 10.35/1.71    sK1 != k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))),
% 10.35/1.71    inference(definition_unfolding,[],[f26,f31,f27,f27])).
% 10.35/1.71  fof(f26,plain,(
% 10.35/1.71    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 10.35/1.71    inference(cnf_transformation,[],[f19])).
% 10.35/1.71  % SZS output end Proof for theBenchmark
% 10.35/1.71  % (15045)------------------------------
% 10.35/1.71  % (15045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.71  % (15045)Termination reason: Refutation
% 10.35/1.71  
% 10.35/1.71  % (15045)Memory used [KB]: 18421
% 10.35/1.71  % (15045)Time elapsed: 1.282 s
% 10.35/1.71  % (15045)------------------------------
% 10.35/1.71  % (15045)------------------------------
% 10.35/1.71  % (15020)Success in time 1.343 s
%------------------------------------------------------------------------------
