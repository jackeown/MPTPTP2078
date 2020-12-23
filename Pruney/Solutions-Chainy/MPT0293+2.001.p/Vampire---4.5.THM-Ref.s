%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:48 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  60 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f48,f15,f60])).

fof(f60,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_tarski(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0)))),X1)
      | ~ r1_tarski(X1,k1_zfmisc_1(k3_tarski(sK0))) ) ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f4])).

% (27320)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0))),X0)
      | ~ r1_tarski(X0,k1_zfmisc_1(k3_tarski(sK0))) ) ),
    inference(resolution,[],[f34,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f34,plain,(
    ~ r2_hidden(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0))),k1_zfmisc_1(k3_tarski(sK0))) ),
    inference(resolution,[],[f14,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    ~ r1_tarski(sK0,k1_zfmisc_1(k3_tarski(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : ~ r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f15,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f48,plain,(
    r1_tarski(k1_zfmisc_1(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0)))),k1_zfmisc_1(k3_tarski(sK0))) ),
    inference(resolution,[],[f37,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f37,plain,(
    r1_tarski(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0))),k3_tarski(sK0)) ),
    inference(resolution,[],[f33,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f33,plain,(
    r2_hidden(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0))),sK0) ),
    inference(resolution,[],[f14,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:00:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.23/0.52  % (27331)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.52  % (27334)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.23/0.53  % (27331)Refutation found. Thanks to Tanya!
% 1.23/0.53  % SZS status Theorem for theBenchmark
% 1.23/0.53  % (27318)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.53  % SZS output start Proof for theBenchmark
% 1.33/0.53  fof(f107,plain,(
% 1.33/0.53    $false),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f48,f15,f60])).
% 1.33/0.53  fof(f60,plain,(
% 1.33/0.53    ( ! [X1] : (~r1_tarski(k1_tarski(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0)))),X1) | ~r1_tarski(X1,k1_zfmisc_1(k3_tarski(sK0)))) )),
% 1.33/0.53    inference(resolution,[],[f39,f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f4])).
% 1.33/0.54  % (27320)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    ( ! [X0] : (~r2_hidden(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0))),X0) | ~r1_tarski(X0,k1_zfmisc_1(k3_tarski(sK0)))) )),
% 1.33/0.54    inference(resolution,[],[f34,f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f13])).
% 1.33/0.54  fof(f13,plain,(
% 1.33/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ~r2_hidden(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0))),k1_zfmisc_1(k3_tarski(sK0)))),
% 1.33/0.54    inference(resolution,[],[f14,f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f13])).
% 1.33/0.54  fof(f14,plain,(
% 1.33/0.54    ~r1_tarski(sK0,k1_zfmisc_1(k3_tarski(sK0)))),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,plain,(
% 1.33/0.54    ? [X0] : ~r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f9])).
% 1.33/0.54  fof(f9,negated_conjecture,(
% 1.33/0.54    ~! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.33/0.54    inference(negated_conjecture,[],[f8])).
% 1.33/0.54  fof(f8,conjecture,(
% 1.33/0.54    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 1.33/0.54  fof(f48,plain,(
% 1.33/0.54    r1_tarski(k1_zfmisc_1(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0)))),k1_zfmisc_1(k3_tarski(sK0)))),
% 1.33/0.54    inference(resolution,[],[f37,f17])).
% 1.33/0.54  fof(f17,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,plain,(
% 1.33/0.54    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.33/0.54  fof(f37,plain,(
% 1.33/0.54    r1_tarski(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0))),k3_tarski(sK0))),
% 1.33/0.54    inference(resolution,[],[f33,f16])).
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f11])).
% 1.33/0.54  fof(f11,plain,(
% 1.33/0.54    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.33/0.54  fof(f33,plain,(
% 1.33/0.54    r2_hidden(sK1(sK0,k1_zfmisc_1(k3_tarski(sK0))),sK0)),
% 1.33/0.54    inference(resolution,[],[f14,f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f13])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (27331)------------------------------
% 1.33/0.54  % (27331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (27331)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (27331)Memory used [KB]: 6268
% 1.33/0.54  % (27331)Time elapsed: 0.114 s
% 1.33/0.54  % (27331)------------------------------
% 1.33/0.54  % (27331)------------------------------
% 1.33/0.54  % (27340)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.54  % (27320)Refutation not found, incomplete strategy% (27320)------------------------------
% 1.33/0.54  % (27320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (27320)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (27320)Memory used [KB]: 10618
% 1.33/0.54  % (27320)Time elapsed: 0.122 s
% 1.33/0.54  % (27320)------------------------------
% 1.33/0.54  % (27320)------------------------------
% 1.33/0.54  % (27317)Success in time 0.178 s
%------------------------------------------------------------------------------
