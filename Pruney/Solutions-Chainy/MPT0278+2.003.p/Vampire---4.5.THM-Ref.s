%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:33 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  76 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1219)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f92,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f54,f84,f52])).

fof(f52,plain,(
    ! [X2] :
      ( r1_tarski(X2,sK1)
      | ~ r1_tarski(X2,sK0) ) ),
    inference(superposition,[],[f43,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),sK1) ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f27,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f12,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f84,plain,(
    ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f31,plain,(
    ~ r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f13,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f13,plain,(
    ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f30,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f30,plain,(
    r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f13,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n022.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 18:07:26 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.53  % (1220)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.20/0.53  % (1206)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.53  % (1211)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.53  % (1212)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.54  % (1213)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.54  % (1208)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.54  % (1209)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.54  % (1228)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.54  % (1210)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.54  % (1208)Refutation not found, incomplete strategy% (1208)------------------------------
% 1.20/0.54  % (1208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.54  % (1208)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.54  
% 1.20/0.54  % (1208)Memory used [KB]: 10618
% 1.20/0.54  % (1208)Time elapsed: 0.116 s
% 1.20/0.54  % (1208)------------------------------
% 1.20/0.54  % (1208)------------------------------
% 1.20/0.54  % (1235)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.20/0.54  % (1207)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.54  % (1210)Refutation found. Thanks to Tanya!
% 1.20/0.54  % SZS status Theorem for theBenchmark
% 1.20/0.54  % SZS output start Proof for theBenchmark
% 1.20/0.54  % (1219)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.54  fof(f92,plain,(
% 1.20/0.54    $false),
% 1.20/0.54    inference(unit_resulting_resolution,[],[f54,f84,f52])).
% 1.20/0.54  fof(f52,plain,(
% 1.20/0.54    ( ! [X2] : (r1_tarski(X2,sK1) | ~r1_tarski(X2,sK0)) )),
% 1.20/0.54    inference(superposition,[],[f43,f19])).
% 1.20/0.54  fof(f19,plain,(
% 1.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.20/0.54    inference(cnf_transformation,[],[f10])).
% 1.20/0.54  fof(f10,plain,(
% 1.20/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.20/0.54    inference(ennf_transformation,[],[f4])).
% 1.20/0.54  fof(f4,axiom,(
% 1.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.20/0.54  fof(f43,plain,(
% 1.20/0.54    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),sK1)) )),
% 1.20/0.54    inference(superposition,[],[f27,f23])).
% 1.20/0.54  fof(f23,plain,(
% 1.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.20/0.54    inference(cnf_transformation,[],[f1])).
% 1.20/0.54  fof(f1,axiom,(
% 1.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.20/0.54  fof(f27,plain,(
% 1.20/0.54    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),sK1)) )),
% 1.20/0.54    inference(unit_resulting_resolution,[],[f12,f18])).
% 1.20/0.54  fof(f18,plain,(
% 1.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.20/0.54    inference(cnf_transformation,[],[f9])).
% 1.20/0.54  fof(f9,plain,(
% 1.20/0.54    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.20/0.54    inference(ennf_transformation,[],[f3])).
% 1.20/0.54  fof(f3,axiom,(
% 1.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.20/0.54  fof(f12,plain,(
% 1.20/0.54    r1_tarski(sK0,sK1)),
% 1.20/0.54    inference(cnf_transformation,[],[f8])).
% 1.20/0.54  fof(f8,plain,(
% 1.20/0.54    ? [X0,X1] : (~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) & r1_tarski(X0,X1))),
% 1.20/0.54    inference(ennf_transformation,[],[f7])).
% 1.20/0.54  fof(f7,negated_conjecture,(
% 1.20/0.54    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.20/0.54    inference(negated_conjecture,[],[f6])).
% 1.20/0.54  fof(f6,conjecture,(
% 1.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.20/0.54  fof(f84,plain,(
% 1.20/0.54    ~r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1)),
% 1.20/0.54    inference(unit_resulting_resolution,[],[f31,f25])).
% 1.20/0.54  fof(f25,plain,(
% 1.20/0.54    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.20/0.54    inference(equality_resolution,[],[f14])).
% 1.20/0.54  fof(f14,plain,(
% 1.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.20/0.54    inference(cnf_transformation,[],[f5])).
% 1.20/0.54  fof(f5,axiom,(
% 1.20/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.20/0.54  fof(f31,plain,(
% 1.20/0.54    ~r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))),
% 1.20/0.54    inference(unit_resulting_resolution,[],[f13,f22])).
% 1.20/0.54  fof(f22,plain,(
% 1.20/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.20/0.54    inference(cnf_transformation,[],[f11])).
% 1.20/0.54  fof(f11,plain,(
% 1.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.20/0.54    inference(ennf_transformation,[],[f2])).
% 1.20/0.54  fof(f2,axiom,(
% 1.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.20/0.54  fof(f13,plain,(
% 1.20/0.54    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),
% 1.20/0.54    inference(cnf_transformation,[],[f8])).
% 1.20/0.54  fof(f54,plain,(
% 1.20/0.54    r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK0)),
% 1.20/0.54    inference(unit_resulting_resolution,[],[f30,f24])).
% 1.20/0.54  fof(f24,plain,(
% 1.20/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.20/0.54    inference(equality_resolution,[],[f15])).
% 1.20/0.54  fof(f15,plain,(
% 1.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.20/0.54    inference(cnf_transformation,[],[f5])).
% 1.20/0.54  fof(f30,plain,(
% 1.20/0.54    r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK0))),
% 1.20/0.54    inference(unit_resulting_resolution,[],[f13,f21])).
% 1.20/0.54  fof(f21,plain,(
% 1.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.20/0.54    inference(cnf_transformation,[],[f11])).
% 1.20/0.54  % SZS output end Proof for theBenchmark
% 1.20/0.54  % (1210)------------------------------
% 1.20/0.54  % (1210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.54  % (1210)Termination reason: Refutation
% 1.20/0.54  
% 1.20/0.54  % (1210)Memory used [KB]: 6268
% 1.20/0.54  % (1210)Time elapsed: 0.117 s
% 1.20/0.54  % (1210)------------------------------
% 1.20/0.54  % (1210)------------------------------
% 1.20/0.54  % (1205)Success in time 0.172 s
%------------------------------------------------------------------------------
