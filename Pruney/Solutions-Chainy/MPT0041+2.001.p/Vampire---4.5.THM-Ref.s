%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:48 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  44 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  97 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f25,f22,f33,f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f33,plain,(
    ~ r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f7,f26,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
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

fof(f26,plain,(
    ~ r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f21,plain,(
    r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f8,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,plain,(
    ~ r1_tarski(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f7,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f22,plain,(
    ~ r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f8,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK2) ),
    inference(unit_resulting_resolution,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (6275)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (6280)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (6297)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (6288)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (6290)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (6295)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (6291)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (6278)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (6291)Refutation not found, incomplete strategy% (6291)------------------------------
% 0.22/0.53  % (6291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6291)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6291)Memory used [KB]: 10618
% 0.22/0.53  % (6291)Time elapsed: 0.120 s
% 0.22/0.53  % (6291)------------------------------
% 0.22/0.53  % (6291)------------------------------
% 1.22/0.53  % (6297)Refutation not found, incomplete strategy% (6297)------------------------------
% 1.22/0.53  % (6297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (6297)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (6297)Memory used [KB]: 10618
% 1.22/0.53  % (6297)Time elapsed: 0.116 s
% 1.22/0.53  % (6297)------------------------------
% 1.22/0.53  % (6297)------------------------------
% 1.22/0.53  % (6278)Refutation found. Thanks to Tanya!
% 1.22/0.53  % SZS status Theorem for theBenchmark
% 1.22/0.53  % SZS output start Proof for theBenchmark
% 1.22/0.53  fof(f218,plain,(
% 1.22/0.53    $false),
% 1.22/0.53    inference(unit_resulting_resolution,[],[f25,f22,f33,f18])).
% 1.22/0.53  fof(f18,plain,(
% 1.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.22/0.53    inference(equality_resolution,[],[f14])).
% 1.22/0.53  fof(f14,plain,(
% 1.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.22/0.53    inference(cnf_transformation,[],[f2])).
% 1.22/0.53  fof(f2,axiom,(
% 1.22/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.22/0.53  fof(f33,plain,(
% 1.22/0.53    ~r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK0)),
% 1.22/0.53    inference(unit_resulting_resolution,[],[f7,f26,f15])).
% 1.22/0.53  fof(f15,plain,(
% 1.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f6])).
% 1.22/0.53  fof(f6,plain,(
% 1.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.22/0.53    inference(ennf_transformation,[],[f1])).
% 1.22/0.53  fof(f1,axiom,(
% 1.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.22/0.53  fof(f26,plain,(
% 1.22/0.53    ~r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK1)),
% 1.22/0.53    inference(unit_resulting_resolution,[],[f21,f19])).
% 1.22/0.53  fof(f19,plain,(
% 1.22/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.22/0.53    inference(equality_resolution,[],[f13])).
% 1.22/0.53  fof(f13,plain,(
% 1.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.22/0.53    inference(cnf_transformation,[],[f2])).
% 1.22/0.53  fof(f21,plain,(
% 1.22/0.53    r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK1))),
% 1.22/0.53    inference(unit_resulting_resolution,[],[f8,f16])).
% 1.22/0.53  fof(f16,plain,(
% 1.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f6])).
% 1.22/0.53  fof(f8,plain,(
% 1.22/0.53    ~r1_tarski(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0))),
% 1.22/0.53    inference(cnf_transformation,[],[f5])).
% 1.22/0.53  fof(f5,plain,(
% 1.22/0.53    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) & r1_tarski(X0,X1))),
% 1.22/0.53    inference(ennf_transformation,[],[f4])).
% 1.22/0.53  fof(f4,negated_conjecture,(
% 1.22/0.53    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.22/0.53    inference(negated_conjecture,[],[f3])).
% 1.22/0.53  fof(f3,conjecture,(
% 1.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.22/0.53  fof(f7,plain,(
% 1.22/0.53    r1_tarski(sK0,sK1)),
% 1.22/0.53    inference(cnf_transformation,[],[f5])).
% 1.22/0.53  fof(f22,plain,(
% 1.22/0.53    ~r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK0))),
% 1.22/0.53    inference(unit_resulting_resolution,[],[f8,f17])).
% 1.22/0.53  fof(f17,plain,(
% 1.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f6])).
% 1.22/0.53  fof(f25,plain,(
% 1.22/0.53    r2_hidden(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK2)),
% 1.22/0.53    inference(unit_resulting_resolution,[],[f21,f20])).
% 1.22/0.53  fof(f20,plain,(
% 1.22/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.22/0.53    inference(equality_resolution,[],[f12])).
% 1.22/0.53  fof(f12,plain,(
% 1.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.22/0.53    inference(cnf_transformation,[],[f2])).
% 1.22/0.53  % SZS output end Proof for theBenchmark
% 1.22/0.53  % (6278)------------------------------
% 1.22/0.53  % (6278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (6278)Termination reason: Refutation
% 1.22/0.53  
% 1.22/0.53  % (6278)Memory used [KB]: 6268
% 1.22/0.53  % (6278)Time elapsed: 0.117 s
% 1.22/0.53  % (6278)------------------------------
% 1.22/0.53  % (6278)------------------------------
% 1.22/0.53  % (6273)Success in time 0.164 s
%------------------------------------------------------------------------------
