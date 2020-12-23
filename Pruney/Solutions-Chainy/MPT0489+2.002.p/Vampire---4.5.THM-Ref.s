%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  22 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(resolution,[],[f29,f9])).

fof(f9,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(duplicate_literal_removal,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
      | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f23,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

% (30533)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
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

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0)),X1),X0)
      | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1) ) ),
    inference(resolution,[],[f19,f8])).

fof(f8,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1)),X2),X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X2) ) ),
    inference(resolution,[],[f13,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (30526)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.49  % (30526)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (30525)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.50  % (30534)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(resolution,[],[f29,f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) & v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f3])).
% 0.21/0.50  fof(f3,conjecture,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 0.21/0.50    inference(resolution,[],[f23,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  % (30533)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0)),X1),X0) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)) )),
% 0.21/0.50    inference(resolution,[],[f19,f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1)),X2),X1) | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X2)) )),
% 0.21/0.50    inference(resolution,[],[f13,f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30526)------------------------------
% 0.21/0.50  % (30526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30526)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30526)Memory used [KB]: 5373
% 0.21/0.50  % (30526)Time elapsed: 0.056 s
% 0.21/0.50  % (30526)------------------------------
% 0.21/0.50  % (30526)------------------------------
% 0.21/0.50  % (30519)Success in time 0.134 s
%------------------------------------------------------------------------------
