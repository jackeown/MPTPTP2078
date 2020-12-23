%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 187 expanded)
%              Number of leaves         :    8 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :   75 ( 282 expanded)
%              Number of equality atoms :   28 ( 148 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(subsumption_resolution,[],[f119,f30])).

fof(f30,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f119,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f118,f104])).

fof(f104,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0))
      | k4_xboole_0(X0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f33,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(X1,k1_xboole_0),X1) ),
    inference(superposition,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f118,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),sK2)) ),
    inference(forward_demodulation,[],[f117,f104])).

fof(f117,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f116,f30])).

fof(f116,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f112,f104])).

fof(f112,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f94,f104])).

fof(f94,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)))
    | ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f93,f38])).

fof(f38,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f13,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f93,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
    | ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f92,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f20,f20])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f92,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))))
    | ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f91,f76])).

fof(f76,plain,(
    ! [X12,X11] : k4_xboole_0(k2_zfmisc_1(sK0,X11),k4_xboole_0(k2_zfmisc_1(sK0,X11),k2_zfmisc_1(sK1,X12))) = k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(superposition,[],[f27,f37])).

fof(f37,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f12,f23])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f19,f20,f20,f20])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f91,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f90,f38])).

fof(f90,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f89,f26])).

fof(f89,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f48,f76])).

fof(f48,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))
    | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2)) ),
    inference(extensionality_resolution,[],[f17,f25])).

fof(f25,plain,(
    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) ),
    inference(definition_unfolding,[],[f14,f20])).

fof(f14,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (24343)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.47  % (24343)Refutation not found, incomplete strategy% (24343)------------------------------
% 0.22/0.47  % (24343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (24343)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (24343)Memory used [KB]: 1663
% 0.22/0.47  % (24343)Time elapsed: 0.061 s
% 0.22/0.47  % (24343)------------------------------
% 0.22/0.47  % (24343)------------------------------
% 0.22/0.50  % (24440)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 0.22/0.50  % (24347)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (24346)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (24352)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (24351)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (24348)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (24344)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (24345)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (24363)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (24367)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (24341)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (24352)Refutation not found, incomplete strategy% (24352)------------------------------
% 0.22/0.54  % (24352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24352)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24352)Memory used [KB]: 10746
% 0.22/0.54  % (24352)Time elapsed: 0.126 s
% 0.22/0.54  % (24352)------------------------------
% 0.22/0.54  % (24352)------------------------------
% 0.22/0.54  % (24371)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (24370)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (24353)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (24362)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (24359)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (24371)Refutation not found, incomplete strategy% (24371)------------------------------
% 0.22/0.54  % (24371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24371)Memory used [KB]: 10746
% 0.22/0.54  % (24371)Time elapsed: 0.131 s
% 0.22/0.54  % (24371)------------------------------
% 0.22/0.54  % (24371)------------------------------
% 0.22/0.54  % (24358)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (24354)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (24350)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (24355)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (24372)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (24354)Refutation not found, incomplete strategy% (24354)------------------------------
% 0.22/0.55  % (24354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24354)Memory used [KB]: 10618
% 0.22/0.55  % (24354)Time elapsed: 0.140 s
% 0.22/0.55  % (24354)------------------------------
% 0.22/0.55  % (24354)------------------------------
% 0.22/0.55  % (24372)Refutation not found, incomplete strategy% (24372)------------------------------
% 0.22/0.55  % (24372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24372)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24372)Memory used [KB]: 1663
% 0.22/0.55  % (24372)Time elapsed: 0.140 s
% 0.22/0.55  % (24372)------------------------------
% 0.22/0.55  % (24372)------------------------------
% 0.22/0.55  % (24365)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (24358)Refutation not found, incomplete strategy% (24358)------------------------------
% 0.22/0.55  % (24358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24358)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24358)Memory used [KB]: 10618
% 0.22/0.55  % (24358)Time elapsed: 0.141 s
% 0.22/0.55  % (24358)------------------------------
% 0.22/0.55  % (24358)------------------------------
% 0.22/0.55  % (24361)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (24369)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (24361)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (24360)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (24356)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.58/0.56  % (24366)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.58/0.57  % (24357)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f120,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(subsumption_resolution,[],[f119,f30])).
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.58/0.57    inference(equality_resolution,[],[f16])).
% 1.58/0.57  fof(f16,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.58/0.57    inference(cnf_transformation,[],[f2])).
% 1.58/0.57  fof(f2,axiom,(
% 1.58/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.58/0.57  fof(f119,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2))),
% 1.58/0.57    inference(forward_demodulation,[],[f118,f104])).
% 1.58/0.57  fof(f104,plain,(
% 1.58/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f102,f45])).
% 1.58/0.57  fof(f45,plain,(
% 1.58/0.57    ( ! [X0] : (r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f29,f24])).
% 1.58/0.57  fof(f24,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f3])).
% 1.58/0.57  fof(f3,axiom,(
% 1.58/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.58/0.57  fof(f29,plain,(
% 1.58/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f22,f20])).
% 1.58/0.57  fof(f20,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f6])).
% 1.58/0.57  fof(f6,axiom,(
% 1.58/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.58/0.57  fof(f22,plain,(
% 1.58/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f5])).
% 1.58/0.57  fof(f5,axiom,(
% 1.58/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.58/0.57  fof(f102,plain,(
% 1.58/0.57    ( ! [X0] : (~r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) | k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.57    inference(resolution,[],[f33,f17])).
% 1.58/0.57  fof(f17,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.58/0.57    inference(cnf_transformation,[],[f2])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,k1_xboole_0),X1)) )),
% 1.58/0.57    inference(superposition,[],[f28,f29])).
% 1.58/0.57  fof(f28,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f21,f20])).
% 1.58/0.57  fof(f21,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f4])).
% 1.58/0.57  fof(f4,axiom,(
% 1.58/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.58/0.57  fof(f118,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),sK2))),
% 1.58/0.57    inference(forward_demodulation,[],[f117,f104])).
% 1.58/0.57  fof(f117,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)))),
% 1.58/0.57    inference(subsumption_resolution,[],[f116,f30])).
% 1.58/0.57  fof(f116,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)))),
% 1.58/0.57    inference(forward_demodulation,[],[f112,f104])).
% 1.58/0.57  fof(f112,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)))),
% 1.58/0.57    inference(backward_demodulation,[],[f94,f104])).
% 1.58/0.57  fof(f94,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0))) | ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2))),
% 1.58/0.57    inference(forward_demodulation,[],[f93,f38])).
% 1.58/0.57  fof(f38,plain,(
% 1.58/0.57    k1_xboole_0 = k4_xboole_0(sK2,sK3)),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f13,f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f3])).
% 1.58/0.57  fof(f13,plain,(
% 1.58/0.57    r1_tarski(sK2,sK3)),
% 1.58/0.57    inference(cnf_transformation,[],[f11])).
% 1.58/0.57  fof(f11,plain,(
% 1.58/0.57    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 1.58/0.57    inference(flattening,[],[f10])).
% 1.58/0.57  fof(f10,plain,(
% 1.58/0.57    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f9])).
% 1.58/0.57  fof(f9,negated_conjecture,(
% 1.58/0.57    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 1.58/0.57    inference(negated_conjecture,[],[f8])).
% 1.58/0.57  fof(f8,conjecture,(
% 1.58/0.57    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 1.58/0.57  fof(f93,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2))),
% 1.58/0.57    inference(forward_demodulation,[],[f92,f26])).
% 1.58/0.57  fof(f26,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f18,f20,f20])).
% 1.58/0.57  fof(f18,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f1])).
% 1.58/0.57  fof(f1,axiom,(
% 1.58/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.58/0.57  fof(f92,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))) | ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2))),
% 1.58/0.57    inference(forward_demodulation,[],[f91,f76])).
% 1.58/0.57  fof(f76,plain,(
% 1.58/0.57    ( ! [X12,X11] : (k4_xboole_0(k2_zfmisc_1(sK0,X11),k4_xboole_0(k2_zfmisc_1(sK0,X11),k2_zfmisc_1(sK1,X12))) = k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 1.58/0.57    inference(superposition,[],[f27,f37])).
% 1.58/0.57  fof(f37,plain,(
% 1.58/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f12,f23])).
% 1.58/0.57  fof(f12,plain,(
% 1.58/0.57    r1_tarski(sK0,sK1)),
% 1.58/0.57    inference(cnf_transformation,[],[f11])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f19,f20,f20,f20])).
% 1.58/0.57  fof(f19,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f7])).
% 1.58/0.57  fof(f7,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 1.58/0.57  fof(f91,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)),k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 1.58/0.57    inference(forward_demodulation,[],[f90,f38])).
% 1.58/0.57  fof(f90,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 1.58/0.57    inference(forward_demodulation,[],[f89,f26])).
% 1.58/0.57  fof(f89,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))),k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 1.58/0.57    inference(backward_demodulation,[],[f48,f76])).
% 1.58/0.57  fof(f48,plain,(
% 1.58/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) | ~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2))),
% 1.58/0.57    inference(extensionality_resolution,[],[f17,f25])).
% 1.58/0.57  fof(f25,plain,(
% 1.58/0.57    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),
% 1.58/0.57    inference(definition_unfolding,[],[f14,f20])).
% 1.58/0.57  fof(f14,plain,(
% 1.58/0.57    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 1.58/0.57    inference(cnf_transformation,[],[f11])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (24361)------------------------------
% 1.58/0.57  % (24361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (24361)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (24361)Memory used [KB]: 1791
% 1.58/0.57  % (24361)Time elapsed: 0.142 s
% 1.58/0.57  % (24361)------------------------------
% 1.58/0.57  % (24361)------------------------------
% 1.58/0.57  % (24349)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.58/0.57  % (24339)Success in time 0.206 s
%------------------------------------------------------------------------------
