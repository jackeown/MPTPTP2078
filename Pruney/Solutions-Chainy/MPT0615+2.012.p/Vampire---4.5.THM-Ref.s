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
% DateTime   : Thu Dec  3 12:51:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 101 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 315 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f24,f83,f82,f86,f54])).

fof(f54,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_hidden(sK2(X2,X4),X5)
      | r1_tarski(X2,X4)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X5) ) ),
    inference(resolution,[],[f40,f20])).

% (24238)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (24235)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

% (24236)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    ~ r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f82,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(global_subsumption,[],[f16,f15,f77])).

fof(f77,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f52,f14])).

fof(f14,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f19,f17])).

fof(f17,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f82,f13])).

fof(f13,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f15,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (24234)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (24249)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (24257)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.49  % (24255)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (24247)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (24255)Refutation not found, incomplete strategy% (24255)------------------------------
% 0.21/0.50  % (24255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24255)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24255)Memory used [KB]: 10618
% 0.21/0.50  % (24255)Time elapsed: 0.050 s
% 0.21/0.50  % (24255)------------------------------
% 0.21/0.50  % (24255)------------------------------
% 0.21/0.50  % (24239)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (24257)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f24,f83,f82,f86,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X4,X2,X5,X3] : (r2_hidden(sK2(X2,X4),X5) | r1_tarski(X2,X4) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X5)) )),
% 0.21/0.51    inference(resolution,[],[f40,f20])).
% 0.21/0.51  % (24238)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (24235)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  % (24236)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f20,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~r2_hidden(sK2(sK0,sK1),sK1)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f82,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(global_subsumption,[],[f16,f15,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | ~r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f52,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((r1_tarski(X0,X1) <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(superposition,[],[f19,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f82,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1)) )),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f15,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (24257)------------------------------
% 0.21/0.51  % (24257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24257)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (24257)Memory used [KB]: 6268
% 0.21/0.51  % (24257)Time elapsed: 0.114 s
% 0.21/0.51  % (24257)------------------------------
% 0.21/0.51  % (24257)------------------------------
% 0.21/0.51  % (24232)Success in time 0.152 s
%------------------------------------------------------------------------------
