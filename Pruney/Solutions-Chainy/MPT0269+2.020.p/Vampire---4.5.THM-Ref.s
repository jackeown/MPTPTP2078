%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:49 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  37 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 (  75 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97,f84])).

fof(f84,plain,(
    sQ2_eqProxy(k4_xboole_0(sK0,k1_tarski(sK1)),k1_xboole_0) ),
    inference(resolution,[],[f63,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ sQ2_eqProxy(X0,X1)
      | sQ2_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f63,plain,(
    sQ2_eqProxy(k1_xboole_0,k4_xboole_0(sK0,k1_tarski(sK1))) ),
    inference(equality_proxy_replacement,[],[f23,f50])).

fof(f23,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f97,plain,(
    ~ sQ2_eqProxy(k4_xboole_0(sK0,k1_tarski(sK1)),k1_xboole_0) ),
    inference(resolution,[],[f90,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ sQ2_eqProxy(k4_xboole_0(X0,X1),k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f40,f50])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f90,plain,(
    ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f87,f62])).

fof(f62,plain,(
    ~ sQ2_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f24,f50])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,
    ( sQ2_eqProxy(k1_xboole_0,sK0)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f82,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(k1_xboole_0,X0)
      | sQ2_eqProxy(k1_tarski(X1),X0)
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(equality_proxy_replacement,[],[f36,f50,f50])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f82,plain,(
    ~ sQ2_eqProxy(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f61,f75])).

fof(f61,plain,(
    ~ sQ2_eqProxy(sK0,k1_tarski(sK1)) ),
    inference(equality_proxy_replacement,[],[f25,f50])).

fof(f25,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (6459)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.48  % (6467)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.48  % (6467)Refutation not found, incomplete strategy% (6467)------------------------------
% 0.20/0.48  % (6467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6467)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (6467)Memory used [KB]: 6140
% 0.20/0.48  % (6467)Time elapsed: 0.003 s
% 0.20/0.48  % (6467)------------------------------
% 0.20/0.48  % (6467)------------------------------
% 1.20/0.52  % (6464)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.52  % (6463)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.20/0.52  % (6465)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.52  % (6465)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f98,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f97,f84])).
% 1.20/0.52  fof(f84,plain,(
% 1.20/0.52    sQ2_eqProxy(k4_xboole_0(sK0,k1_tarski(sK1)),k1_xboole_0)),
% 1.20/0.52    inference(resolution,[],[f63,f75])).
% 1.20/0.52  fof(f75,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~sQ2_eqProxy(X0,X1) | sQ2_eqProxy(X1,X0)) )),
% 1.20/0.52    inference(equality_proxy_axiom,[],[f50])).
% 1.20/0.52  fof(f50,plain,(
% 1.20/0.52    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 1.20/0.52    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 1.20/0.52  fof(f63,plain,(
% 1.20/0.52    sQ2_eqProxy(k1_xboole_0,k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.20/0.52    inference(equality_proxy_replacement,[],[f23,f50])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.20/0.52    inference(ennf_transformation,[],[f21])).
% 1.20/0.52  fof(f21,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.20/0.52    inference(negated_conjecture,[],[f20])).
% 1.20/0.52  fof(f20,conjecture,(
% 1.20/0.52    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.20/0.52  fof(f97,plain,(
% 1.20/0.52    ~sQ2_eqProxy(k4_xboole_0(sK0,k1_tarski(sK1)),k1_xboole_0)),
% 1.20/0.52    inference(resolution,[],[f90,f70])).
% 1.20/0.52  fof(f70,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~sQ2_eqProxy(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 1.20/0.52    inference(equality_proxy_replacement,[],[f40,f50])).
% 1.20/0.52  fof(f40,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.20/0.52  fof(f90,plain,(
% 1.20/0.52    ~r1_tarski(sK0,k1_tarski(sK1))),
% 1.20/0.52    inference(subsumption_resolution,[],[f87,f62])).
% 1.20/0.52  fof(f62,plain,(
% 1.20/0.52    ~sQ2_eqProxy(k1_xboole_0,sK0)),
% 1.20/0.52    inference(equality_proxy_replacement,[],[f24,f50])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    k1_xboole_0 != sK0),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f87,plain,(
% 1.20/0.52    sQ2_eqProxy(k1_xboole_0,sK0) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 1.20/0.52    inference(resolution,[],[f82,f69])).
% 1.20/0.52  fof(f69,plain,(
% 1.20/0.52    ( ! [X0,X1] : (sQ2_eqProxy(k1_xboole_0,X0) | sQ2_eqProxy(k1_tarski(X1),X0) | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.20/0.52    inference(equality_proxy_replacement,[],[f36,f50,f50])).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f19,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 1.20/0.52  fof(f82,plain,(
% 1.20/0.52    ~sQ2_eqProxy(k1_tarski(sK1),sK0)),
% 1.20/0.52    inference(resolution,[],[f61,f75])).
% 1.20/0.52  fof(f61,plain,(
% 1.20/0.52    ~sQ2_eqProxy(sK0,k1_tarski(sK1))),
% 1.20/0.52    inference(equality_proxy_replacement,[],[f25,f50])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    sK0 != k1_tarski(sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (6465)------------------------------
% 1.20/0.52  % (6465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (6465)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (6465)Memory used [KB]: 6140
% 1.20/0.52  % (6465)Time elapsed: 0.106 s
% 1.20/0.52  % (6465)------------------------------
% 1.20/0.52  % (6465)------------------------------
% 1.20/0.52  % (6466)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.20/0.53  % (6453)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.53  % (6480)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.20/0.53  % (6474)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.53  % (6454)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (6452)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.53  % (6472)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.53  % (6452)Refutation not found, incomplete strategy% (6452)------------------------------
% 1.32/0.53  % (6452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (6452)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (6452)Memory used [KB]: 1663
% 1.32/0.53  % (6452)Time elapsed: 0.114 s
% 1.32/0.53  % (6452)------------------------------
% 1.32/0.53  % (6452)------------------------------
% 1.32/0.53  % (6456)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (6455)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (6457)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (6451)Success in time 0.178 s
%------------------------------------------------------------------------------
