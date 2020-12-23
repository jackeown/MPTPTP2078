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
% DateTime   : Thu Dec  3 12:50:08 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 (  80 expanded)
%              Number of equality atoms :   33 (  44 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f101,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f101,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f91,f44])).

fof(f44,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f91,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f45,f81])).

fof(f81,plain,(
    k1_xboole_0 = k2_tarski(sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0)) ),
    inference(unit_resulting_resolution,[],[f57,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f57,plain,(
    r1_tarski(k2_tarski(sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f55,plain,(
    r2_hidden(sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f22,f50,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f50,plain,(
    r2_hidden(sK2(k10_relat_1(sK0,k1_xboole_0)),k10_relat_1(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f23,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X1] : k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k1_setfam_1(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)))) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k5_xboole_0(k2_tarski(X0,X0),k1_setfam_1(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) ) ),
    inference(definition_unfolding,[],[f35,f36,f39,f36,f36])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.07/0.25  % Computer   : n004.cluster.edu
% 0.07/0.25  % Model      : x86_64 x86_64
% 0.07/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.25  % Memory     : 8042.1875MB
% 0.07/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.25  % CPULimit   : 60
% 0.07/0.25  % WCLimit    : 600
% 0.07/0.25  % DateTime   : Tue Dec  1 18:35:23 EST 2020
% 0.07/0.25  % CPUTime    : 
% 0.12/0.40  % (24846)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.41  % (24845)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.12/0.41  % (24842)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.12/0.41  % (24836)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.12/0.41  % (24838)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.12/0.41  % (24838)Refutation found. Thanks to Tanya!
% 0.12/0.41  % SZS status Theorem for theBenchmark
% 0.12/0.42  % (24839)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.12/0.42  % (24845)Refutation not found, incomplete strategy% (24845)------------------------------
% 0.12/0.42  % (24845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (24845)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (24845)Memory used [KB]: 10618
% 0.12/0.42  % (24845)Time elapsed: 0.102 s
% 0.12/0.42  % (24845)------------------------------
% 0.12/0.42  % (24845)------------------------------
% 0.12/0.42  % (24844)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.12/0.42  % (24844)Refutation not found, incomplete strategy% (24844)------------------------------
% 0.12/0.42  % (24844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (24844)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (24844)Memory used [KB]: 10618
% 0.12/0.42  % (24844)Time elapsed: 0.108 s
% 0.12/0.42  % (24844)------------------------------
% 0.12/0.42  % (24844)------------------------------
% 0.12/0.42  % (24856)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.12/0.42  % (24856)Refutation not found, incomplete strategy% (24856)------------------------------
% 0.12/0.42  % (24856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (24856)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (24856)Memory used [KB]: 10618
% 0.12/0.42  % (24856)Time elapsed: 0.073 s
% 0.12/0.42  % (24856)------------------------------
% 0.12/0.42  % (24856)------------------------------
% 0.12/0.42  % (24836)Refutation not found, incomplete strategy% (24836)------------------------------
% 0.12/0.42  % (24836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (24836)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (24836)Memory used [KB]: 10618
% 0.12/0.42  % (24836)Time elapsed: 0.109 s
% 0.12/0.42  % (24836)------------------------------
% 0.12/0.42  % (24836)------------------------------
% 0.12/0.42  % (24852)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.12/0.42  % SZS output start Proof for theBenchmark
% 0.12/0.42  fof(f114,plain,(
% 0.12/0.42    $false),
% 0.12/0.42    inference(trivial_inequality_removal,[],[f113])).
% 0.12/0.42  fof(f113,plain,(
% 0.12/0.42    k1_xboole_0 != k1_xboole_0),
% 0.12/0.42    inference(superposition,[],[f101,f30])).
% 0.12/0.42  fof(f30,plain,(
% 0.12/0.42    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f4])).
% 0.12/0.42  fof(f4,axiom,(
% 0.12/0.42    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.12/0.42  fof(f101,plain,(
% 0.12/0.42    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.12/0.42    inference(forward_demodulation,[],[f91,f44])).
% 0.12/0.42  fof(f44,plain,(
% 0.12/0.42    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 0.12/0.42    inference(definition_unfolding,[],[f37,f36])).
% 0.12/0.42  fof(f36,plain,(
% 0.12/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f5])).
% 0.12/0.42  fof(f5,axiom,(
% 0.12/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.12/0.42  fof(f37,plain,(
% 0.12/0.42    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.12/0.42    inference(cnf_transformation,[],[f13])).
% 0.12/0.42  fof(f13,axiom,(
% 0.12/0.42    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.12/0.42  fof(f91,plain,(
% 0.12/0.42    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)))),
% 0.12/0.42    inference(superposition,[],[f45,f81])).
% 0.12/0.42  fof(f81,plain,(
% 0.12/0.42    k1_xboole_0 = k2_tarski(sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0))),
% 0.12/0.42    inference(unit_resulting_resolution,[],[f57,f29])).
% 0.12/0.42  fof(f29,plain,(
% 0.12/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.12/0.42    inference(cnf_transformation,[],[f21])).
% 0.12/0.42  fof(f21,plain,(
% 0.12/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.12/0.42    inference(ennf_transformation,[],[f3])).
% 0.12/0.42  fof(f3,axiom,(
% 0.12/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.12/0.42  fof(f57,plain,(
% 0.12/0.42    r1_tarski(k2_tarski(sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0)),k1_xboole_0)),
% 0.12/0.42    inference(unit_resulting_resolution,[],[f55,f41])).
% 0.12/0.42  fof(f41,plain,(
% 0.12/0.42    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.12/0.42    inference(definition_unfolding,[],[f31,f36])).
% 0.12/0.42  fof(f31,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f11])).
% 0.12/0.42  fof(f11,axiom,(
% 0.12/0.42    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.12/0.42  fof(f55,plain,(
% 0.12/0.42    r2_hidden(sK1(sK2(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),k1_xboole_0)),
% 0.12/0.42    inference(unit_resulting_resolution,[],[f22,f50,f26])).
% 0.12/0.42  fof(f26,plain,(
% 0.12/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f19])).
% 0.12/0.42  fof(f19,plain,(
% 0.12/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.12/0.42    inference(ennf_transformation,[],[f15])).
% 0.12/0.42  fof(f15,axiom,(
% 0.12/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.12/0.42  fof(f50,plain,(
% 0.12/0.42    r2_hidden(sK2(k10_relat_1(sK0,k1_xboole_0)),k10_relat_1(sK0,k1_xboole_0))),
% 0.12/0.42    inference(unit_resulting_resolution,[],[f23,f28])).
% 0.12/0.42  fof(f28,plain,(
% 0.12/0.42    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.12/0.42    inference(cnf_transformation,[],[f20])).
% 0.12/0.42  fof(f20,plain,(
% 0.12/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.12/0.42    inference(ennf_transformation,[],[f1])).
% 0.12/0.42  fof(f1,axiom,(
% 0.12/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.12/0.42  fof(f23,plain,(
% 0.12/0.42    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.12/0.42    inference(cnf_transformation,[],[f18])).
% 0.12/0.42  fof(f18,plain,(
% 0.12/0.42    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.12/0.42    inference(ennf_transformation,[],[f17])).
% 0.12/0.42  fof(f17,negated_conjecture,(
% 0.12/0.42    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.12/0.42    inference(negated_conjecture,[],[f16])).
% 0.12/0.42  fof(f16,conjecture,(
% 0.12/0.42    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.12/0.42  fof(f22,plain,(
% 0.12/0.42    v1_relat_1(sK0)),
% 0.12/0.42    inference(cnf_transformation,[],[f18])).
% 0.12/0.42  fof(f45,plain,(
% 0.12/0.42    ( ! [X1] : (k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k1_setfam_1(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1))))) )),
% 0.12/0.42    inference(equality_resolution,[],[f42])).
% 0.12/0.42  fof(f42,plain,(
% 0.12/0.42    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k5_xboole_0(k2_tarski(X0,X0),k1_setfam_1(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))))) )),
% 0.12/0.42    inference(definition_unfolding,[],[f35,f36,f39,f36,f36])).
% 0.12/0.42  fof(f39,plain,(
% 0.12/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.12/0.42    inference(definition_unfolding,[],[f33,f38])).
% 0.12/0.42  fof(f38,plain,(
% 0.12/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f14])).
% 0.12/0.42  fof(f14,axiom,(
% 0.12/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.12/0.42  fof(f33,plain,(
% 0.12/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f2])).
% 0.12/0.42  fof(f2,axiom,(
% 0.12/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.12/0.42  fof(f35,plain,(
% 0.12/0.42    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f12])).
% 0.12/0.42  fof(f12,axiom,(
% 0.12/0.42    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.12/0.42  % SZS output end Proof for theBenchmark
% 0.12/0.42  % (24838)------------------------------
% 0.12/0.42  % (24838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (24838)Termination reason: Refutation
% 0.12/0.42  
% 0.12/0.42  % (24838)Memory used [KB]: 6268
% 0.12/0.42  % (24838)Time elapsed: 0.099 s
% 0.12/0.42  % (24838)------------------------------
% 0.12/0.42  % (24838)------------------------------
% 0.12/0.43  % (24833)Success in time 0.159 s
%------------------------------------------------------------------------------
