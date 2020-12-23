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
% DateTime   : Thu Dec  3 12:50:41 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   34 (  55 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  75 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(subsumption_resolution,[],[f55,f51])).

fof(f51,plain,(
    ! [X6,X7] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,X6),k10_relat_1(sK2,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f55,plain,(
    k1_xboole_0 != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f54,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f54,plain,(
    k1_xboole_0 != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f53,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f53,plain,(
    k1_xboole_0 != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f52,f43])).

fof(f52,plain,(
    k1_xboole_0 != k6_subset_1(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))) ),
    inference(superposition,[],[f45,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f32,f30,f30,f30])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f45,plain,(
    k1_xboole_0 != k6_subset_1(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f28,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:55:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 1.19/0.51  % (24780)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.19/0.51  % (24764)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.51  % (24771)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.19/0.51  % (24765)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.19/0.51  % (24774)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.19/0.52  % (24757)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.52  % (24782)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.19/0.52  % (24775)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.19/0.52  % (24769)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.19/0.52  % (24760)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.19/0.52  % (24761)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.52  % (24758)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (24779)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.53  % (24756)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.53  % (24762)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.53  % (24773)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.53  % (24783)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.53  % (24773)Refutation not found, incomplete strategy% (24773)------------------------------
% 1.30/0.53  % (24773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (24773)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (24773)Memory used [KB]: 10618
% 1.30/0.53  % (24773)Time elapsed: 0.131 s
% 1.30/0.53  % (24773)------------------------------
% 1.30/0.53  % (24773)------------------------------
% 1.30/0.53  % (24784)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.53  % (24777)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.53  % (24765)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f56,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(subsumption_resolution,[],[f55,f51])).
% 1.30/0.53  fof(f51,plain,(
% 1.30/0.53    ( ! [X6,X7] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,X6),k10_relat_1(sK2,k2_xboole_0(X6,X7)))) )),
% 1.30/0.53    inference(superposition,[],[f41,f43])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.30/0.53    inference(unit_resulting_resolution,[],[f27,f31])).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f26])).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.30/0.53    inference(ennf_transformation,[],[f18])).
% 1.30/0.53  fof(f18,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    v1_relat_1(sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 1.30/0.53    inference(ennf_transformation,[],[f22])).
% 1.30/0.53  fof(f22,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.30/0.53    inference(negated_conjecture,[],[f21])).
% 1.30/0.53  fof(f21,conjecture,(
% 1.30/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f34,f30])).
% 1.30/0.53  fof(f30,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f13])).
% 1.30/0.53  fof(f13,axiom,(
% 1.30/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f7])).
% 1.30/0.53  fof(f7,axiom,(
% 1.30/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.30/0.53  fof(f55,plain,(
% 1.30/0.53    k1_xboole_0 != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))),
% 1.30/0.53    inference(forward_demodulation,[],[f54,f36])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    k1_xboole_0 != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,sK0)))),
% 1.30/0.53    inference(forward_demodulation,[],[f53,f40])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f33,f30])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    k1_xboole_0 != k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))),
% 1.30/0.53    inference(forward_demodulation,[],[f52,f43])).
% 1.30/0.53  fof(f52,plain,(
% 1.30/0.53    k1_xboole_0 != k6_subset_1(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k6_subset_1(sK0,sK1))))),
% 1.30/0.53    inference(superposition,[],[f45,f39])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k2_xboole_0(X1,X2))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f32,f30,f30,f30])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f6])).
% 1.30/0.53  fof(f6,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.30/0.53  fof(f45,plain,(
% 1.30/0.53    k1_xboole_0 != k6_subset_1(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 1.30/0.53    inference(unit_resulting_resolution,[],[f28,f38])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(definition_unfolding,[],[f29,f30])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f25])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 1.30/0.53    inference(ennf_transformation,[],[f23])).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 1.30/0.53    inference(unused_predicate_definition_removal,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 1.30/0.53    inference(cnf_transformation,[],[f24])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (24765)------------------------------
% 1.30/0.53  % (24765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (24765)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (24765)Memory used [KB]: 10618
% 1.30/0.53  % (24765)Time elapsed: 0.115 s
% 1.30/0.53  % (24765)------------------------------
% 1.30/0.53  % (24765)------------------------------
% 1.30/0.54  % (24755)Success in time 0.182 s
%------------------------------------------------------------------------------
