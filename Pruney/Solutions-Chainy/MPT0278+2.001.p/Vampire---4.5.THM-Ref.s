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
% DateTime   : Thu Dec  3 12:41:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  57 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 126 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f63,f61,f81,f108])).

fof(f108,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(X8,X9),sK1)
      | ~ r1_tarski(X8,sK0)
      | r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f53,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,sK1)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f39,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f13,f18])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

% (10042)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f81,plain,(
    ~ r2_hidden(sK2(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1),sK1) ),
    inference(resolution,[],[f63,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK0) ),
    inference(resolution,[],[f44,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f44,plain,(
    r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f14,f19])).

fof(f14,plain,(
    ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    ~ r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1) ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ~ r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f14,f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:59:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (10045)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (10062)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (10051)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (10051)Refutation not found, incomplete strategy% (10051)------------------------------
% 0.21/0.52  % (10051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10051)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10051)Memory used [KB]: 10618
% 0.21/0.52  % (10051)Time elapsed: 0.118 s
% 0.21/0.52  % (10051)------------------------------
% 0.21/0.52  % (10051)------------------------------
% 0.21/0.52  % (10054)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (10054)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (10041)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (10043)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f63,f61,f81,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X8,X9] : (r2_hidden(sK2(X8,X9),sK1) | ~r1_tarski(X8,sK0) | r1_tarski(X8,X9)) )),
% 0.21/0.53    inference(resolution,[],[f53,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,sK1) | ~r1_tarski(X1,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f39,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f13,f18])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  % (10042)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1] : (~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) & r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ~r2_hidden(sK2(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1),sK1)),
% 0.21/0.53    inference(resolution,[],[f63,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK0)),
% 0.21/0.53    inference(resolution,[],[f44,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f14,f19])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ~r1_tarski(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1)),
% 0.21/0.53    inference(resolution,[],[f45,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~r2_hidden(sK2(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))),
% 0.21/0.54    inference(resolution,[],[f14,f20])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (10054)------------------------------
% 0.21/0.54  % (10054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10054)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (10054)Memory used [KB]: 6268
% 0.21/0.54  % (10054)Time elapsed: 0.124 s
% 0.21/0.54  % (10054)------------------------------
% 0.21/0.54  % (10054)------------------------------
% 0.21/0.54  % (10047)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (10043)Refutation not found, incomplete strategy% (10043)------------------------------
% 0.21/0.54  % (10043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10043)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10043)Memory used [KB]: 10618
% 0.21/0.54  % (10043)Time elapsed: 0.124 s
% 0.21/0.54  % (10043)------------------------------
% 0.21/0.54  % (10043)------------------------------
% 0.21/0.54  % (10040)Success in time 0.172 s
%------------------------------------------------------------------------------
