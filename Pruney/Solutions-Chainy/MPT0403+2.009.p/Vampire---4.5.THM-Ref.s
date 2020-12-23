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
% DateTime   : Thu Dec  3 12:46:17 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   31 (  54 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  97 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(global_subsumption,[],[f73,f137])).

fof(f137,plain,(
    sP3(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0,sK0) ),
    inference(forward_demodulation,[],[f135,f28])).

fof(f28,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f135,plain,(
    sP3(k3_tarski(k2_tarski(sK1(sK0,k2_setfam_1(sK0,sK0)),sK1(sK0,k2_setfam_1(sK0,sK0)))),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f35,f35,f33])).

fof(f33,plain,(
    ! [X4,X0,X5,X1] :
      ( sP3(k3_tarski(k2_tarski(X4,X5)),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(k2_tarski(X4,X5)) != X3
      | sP3(X3,X1,X0) ) ),
    inference(definition_unfolding,[],[f20,f15])).

fof(f15,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f20,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k2_xboole_0(X4,X5) != X3
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).

fof(f35,plain,(
    r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f34,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f34,plain,(
    ~ r1_tarski(sK0,k2_setfam_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f12,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f12,plain,(
    ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).

fof(f73,plain,(
    ~ sP3(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f36,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_setfam_1(X0,X1))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),k2_setfam_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 16:36:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (24390)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (24390)Refutation not found, incomplete strategy% (24390)------------------------------
% 0.21/0.53  % (24390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (24390)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  % (24394)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.55  
% 1.45/0.55  % (24390)Memory used [KB]: 10618
% 1.45/0.55  % (24390)Time elapsed: 0.116 s
% 1.45/0.55  % (24390)------------------------------
% 1.45/0.55  % (24390)------------------------------
% 1.45/0.55  % (24385)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.45/0.56  % (24398)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (24384)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.56  % (24387)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.56  % (24395)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.57  % (24406)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.57  % (24386)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.57  % (24384)Refutation not found, incomplete strategy% (24384)------------------------------
% 1.45/0.57  % (24384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (24384)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (24384)Memory used [KB]: 10618
% 1.45/0.57  % (24384)Time elapsed: 0.146 s
% 1.45/0.57  % (24384)------------------------------
% 1.45/0.57  % (24384)------------------------------
% 1.45/0.57  % (24406)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.57  % SZS output start Proof for theBenchmark
% 1.45/0.57  fof(f138,plain,(
% 1.45/0.57    $false),
% 1.45/0.57    inference(global_subsumption,[],[f73,f137])).
% 1.45/0.57  fof(f137,plain,(
% 1.45/0.57    sP3(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0,sK0)),
% 1.45/0.57    inference(forward_demodulation,[],[f135,f28])).
% 1.45/0.57  fof(f28,plain,(
% 1.45/0.57    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 1.45/0.57    inference(definition_unfolding,[],[f13,f14])).
% 1.45/0.57  fof(f14,plain,(
% 1.45/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f2])).
% 1.45/0.57  fof(f2,axiom,(
% 1.45/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.57  fof(f13,plain,(
% 1.45/0.57    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.45/0.57    inference(cnf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.45/0.57  fof(f135,plain,(
% 1.45/0.57    sP3(k3_tarski(k2_tarski(sK1(sK0,k2_setfam_1(sK0,sK0)),sK1(sK0,k2_setfam_1(sK0,sK0)))),sK0,sK0)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f35,f35,f33])).
% 1.45/0.57  fof(f33,plain,(
% 1.45/0.57    ( ! [X4,X0,X5,X1] : (sP3(k3_tarski(k2_tarski(X4,X5)),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f30])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k3_tarski(k2_tarski(X4,X5)) != X3 | sP3(X3,X1,X0)) )),
% 1.45/0.57    inference(definition_unfolding,[],[f20,f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k2_xboole_0(X4,X5) != X3 | sP3(X3,X1,X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f5])).
% 1.45/0.57  fof(f5,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).
% 1.45/0.57  fof(f35,plain,(
% 1.45/0.57    r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f34,f18])).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  fof(f11,plain,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f1])).
% 1.45/0.57  fof(f1,axiom,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    ~r1_tarski(sK0,k2_setfam_1(sK0,sK0))),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f12,f16])).
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_setfam_1(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f10])).
% 1.45/0.57  fof(f10,plain,(
% 1.45/0.57    ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1))),
% 1.45/0.57    inference(ennf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,axiom,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).
% 1.45/0.57  fof(f12,plain,(
% 1.45/0.57    ~r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))),
% 1.45/0.57    inference(cnf_transformation,[],[f9])).
% 1.45/0.57  fof(f9,plain,(
% 1.45/0.57    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f8])).
% 1.45/0.57  fof(f8,negated_conjecture,(
% 1.45/0.57    ~! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 1.45/0.57    inference(negated_conjecture,[],[f7])).
% 1.45/0.57  fof(f7,conjecture,(
% 1.45/0.57    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).
% 1.45/0.57  fof(f73,plain,(
% 1.45/0.57    ~sP3(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0,sK0)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f36,f32])).
% 1.45/0.57  fof(f32,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_setfam_1(X0,X1)) | ~sP3(X3,X1,X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f24])).
% 1.45/0.57  fof(f24,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_setfam_1(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f5])).
% 1.45/0.57  fof(f36,plain,(
% 1.45/0.57    ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),k2_setfam_1(sK0,sK0))),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f34,f19])).
% 1.45/0.57  fof(f19,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  % SZS output end Proof for theBenchmark
% 1.45/0.57  % (24406)------------------------------
% 1.45/0.57  % (24406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (24406)Termination reason: Refutation
% 1.45/0.57  
% 1.45/0.57  % (24406)Memory used [KB]: 6268
% 1.45/0.57  % (24406)Time elapsed: 0.147 s
% 1.45/0.57  % (24406)------------------------------
% 1.45/0.57  % (24406)------------------------------
% 1.45/0.57  % (24409)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.62/0.57  % (24381)Success in time 0.21 s
%------------------------------------------------------------------------------
