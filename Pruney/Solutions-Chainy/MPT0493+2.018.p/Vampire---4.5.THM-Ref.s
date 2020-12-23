%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  93 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :   15
%              Number of atoms          :   86 ( 265 expanded)
%              Number of equality atoms :   18 (  66 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f117,f14])).

fof(f14,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f8])).

% (7480)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f8,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f117,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f114,f106])).

fof(f106,plain,(
    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f103,f14])).

fof(f103,plain,
    ( r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
    | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(factoring,[],[f90])).

fof(f90,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2,sK0),X2)
      | r2_hidden(sK2(X2,sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
      | sK0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X2] :
      ( sK0 = X2
      | r2_hidden(sK2(X2,sK0),X2)
      | r2_hidden(sK2(X2,sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
      | r2_hidden(sK2(X2,sK0),X2)
      | sK0 = X2 ) ),
    inference(resolution,[],[f40,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,sK0),X1)
      | sK0 = X0
      | r2_hidden(sK2(X0,sK0),X0)
      | r2_hidden(sK2(X0,sK0),k1_relat_1(k7_relat_1(sK1,X1))) ) ),
    inference(resolution,[],[f34,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) ) ),
    inference(resolution,[],[f20,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

% (7500)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,sK0),X0)
      | r2_hidden(sK2(X0,sK0),k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(resolution,[],[f21,f13])).

fof(f13,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X2) ) ),
    inference(resolution,[],[f15,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f114,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
    | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f112,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f112,plain,(
    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),sK0) ),
    inference(subsumption_resolution,[],[f109,f12])).

fof(f109,plain,
    ( r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f106,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:14:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (7483)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (7499)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (7492)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (7491)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (7483)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f117,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  % (7480)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f4])).
% 0.22/0.52  fof(f4,conjecture,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f103,f14])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.52    inference(factoring,[],[f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X2] : (r2_hidden(sK2(X2,sK0),X2) | r2_hidden(sK2(X2,sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | sK0 = X2) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X2] : (sK0 = X2 | r2_hidden(sK2(X2,sK0),X2) | r2_hidden(sK2(X2,sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | r2_hidden(sK2(X2,sK0),X2) | sK0 = X2) )),
% 0.22/0.52    inference(resolution,[],[f40,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,sK0),X1) | sK0 = X0 | r2_hidden(sK2(X0,sK0),X0) | r2_hidden(sK2(X0,sK0),k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 0.22/0.52    inference(resolution,[],[f34,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 0.22/0.52    inference(resolution,[],[f20,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.52  % (7500)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK2(X0,sK0),X0) | r2_hidden(sK2(X0,sK0),k1_relat_1(sK1)) | sK0 = X0) )),
% 0.22/0.52    inference(resolution,[],[f21,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | X0 = X1 | r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X2)) )),
% 0.22/0.52    inference(resolution,[],[f15,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.52    inference(resolution,[],[f112,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f109,f12])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f106,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (7483)------------------------------
% 0.22/0.52  % (7483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7483)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (7483)Memory used [KB]: 6268
% 0.22/0.52  % (7483)Time elapsed: 0.106 s
% 0.22/0.52  % (7483)------------------------------
% 0.22/0.52  % (7483)------------------------------
% 0.22/0.52  % (7476)Success in time 0.159 s
%------------------------------------------------------------------------------
