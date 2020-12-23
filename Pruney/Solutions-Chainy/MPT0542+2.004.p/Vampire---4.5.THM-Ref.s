%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:19 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   19 (  28 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  62 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f9,f28,f31,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f31,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f29,f23])).

fof(f23,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f29,plain,(
    ~ r2_hidden(sK2(k9_relat_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f10,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f10,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f28,plain,(
    r2_hidden(sK2(k9_relat_1(sK1,sK0),k2_relat_1(sK1)),k9_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f10,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.18/0.51  % (16486)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.18/0.51  % (16486)Refutation not found, incomplete strategy% (16486)------------------------------
% 1.18/0.51  % (16486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.51  % (16474)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.18/0.51  % (16486)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.51  
% 1.18/0.51  % (16486)Memory used [KB]: 10618
% 1.18/0.51  % (16486)Time elapsed: 0.041 s
% 1.18/0.51  % (16486)------------------------------
% 1.18/0.51  % (16486)------------------------------
% 1.18/0.51  % (16472)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.18/0.51  % (16467)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.18/0.52  % (16472)Refutation not found, incomplete strategy% (16472)------------------------------
% 1.18/0.52  % (16472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (16472)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (16472)Memory used [KB]: 10618
% 1.18/0.52  % (16472)Time elapsed: 0.045 s
% 1.18/0.52  % (16472)------------------------------
% 1.18/0.52  % (16472)------------------------------
% 1.18/0.52  % (16468)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.18/0.52  % (16468)Refutation found. Thanks to Tanya!
% 1.18/0.52  % SZS status Theorem for theBenchmark
% 1.18/0.52  % SZS output start Proof for theBenchmark
% 1.18/0.52  fof(f40,plain,(
% 1.18/0.52    $false),
% 1.18/0.52    inference(unit_resulting_resolution,[],[f9,f28,f31,f19])).
% 1.18/0.52  fof(f19,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f8])).
% 1.18/0.52  fof(f8,plain,(
% 1.18/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.18/0.52    inference(ennf_transformation,[],[f3])).
% 1.18/0.52  fof(f3,axiom,(
% 1.18/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.18/0.52  fof(f31,plain,(
% 1.18/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK1)) )),
% 1.18/0.52    inference(unit_resulting_resolution,[],[f29,f23])).
% 1.18/0.52  fof(f23,plain,(
% 1.18/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.18/0.52    inference(equality_resolution,[],[f14])).
% 1.18/0.52  fof(f14,plain,(
% 1.18/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.18/0.52    inference(cnf_transformation,[],[f2])).
% 1.18/0.52  fof(f2,axiom,(
% 1.18/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.18/0.52  fof(f29,plain,(
% 1.18/0.52    ~r2_hidden(sK2(k9_relat_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 1.18/0.52    inference(unit_resulting_resolution,[],[f10,f13])).
% 1.18/0.52  fof(f13,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f7])).
% 1.18/0.52  fof(f7,plain,(
% 1.18/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.18/0.52    inference(ennf_transformation,[],[f1])).
% 1.18/0.52  fof(f1,axiom,(
% 1.18/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.18/0.52  fof(f10,plain,(
% 1.18/0.52    ~r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 1.18/0.52    inference(cnf_transformation,[],[f6])).
% 1.18/0.52  fof(f6,plain,(
% 1.18/0.52    ? [X0,X1] : (~r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) & v1_relat_1(X1))),
% 1.18/0.52    inference(ennf_transformation,[],[f5])).
% 1.18/0.52  fof(f5,negated_conjecture,(
% 1.18/0.52    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.18/0.52    inference(negated_conjecture,[],[f4])).
% 1.18/0.52  fof(f4,conjecture,(
% 1.18/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.18/0.52  fof(f28,plain,(
% 1.18/0.52    r2_hidden(sK2(k9_relat_1(sK1,sK0),k2_relat_1(sK1)),k9_relat_1(sK1,sK0))),
% 1.18/0.52    inference(unit_resulting_resolution,[],[f10,f12])).
% 1.18/0.52  fof(f12,plain,(
% 1.18/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f7])).
% 1.18/0.52  fof(f9,plain,(
% 1.18/0.52    v1_relat_1(sK1)),
% 1.18/0.52    inference(cnf_transformation,[],[f6])).
% 1.18/0.52  % SZS output end Proof for theBenchmark
% 1.18/0.52  % (16468)------------------------------
% 1.18/0.52  % (16468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (16468)Termination reason: Refutation
% 1.18/0.52  
% 1.18/0.52  % (16468)Memory used [KB]: 6140
% 1.18/0.52  % (16468)Time elapsed: 0.099 s
% 1.18/0.52  % (16468)------------------------------
% 1.18/0.52  % (16468)------------------------------
% 1.18/0.52  % (16458)Success in time 0.163 s
%------------------------------------------------------------------------------
