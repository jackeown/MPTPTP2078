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
% DateTime   : Thu Dec  3 12:48:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   26 (  40 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 (  91 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f164,f78])).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),X0),k7_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f12,f32,f47,f31])).

% (5784)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (5797)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (5802)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (5801)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f31,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f47,plain,(
    ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f13,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f13,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f12,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f164,plain,(
    r2_hidden(k4_tarski(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),sK4(k7_relat_1(sK1,sK0),sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0))),k7_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f46,plain,(
    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f13,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:54:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (5793)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (5792)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (5789)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (5800)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (5785)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (5808)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (5791)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (5793)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (5788)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (5806)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (5786)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (5787)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (5804)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (5796)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (5798)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (5813)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (5794)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.54  % (5806)Refutation not found, incomplete strategy% (5806)------------------------------
% 1.41/0.54  % (5806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (5809)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.54  % (5806)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.55  % (5806)Memory used [KB]: 10618
% 1.41/0.55  % (5806)Time elapsed: 0.084 s
% 1.41/0.55  % (5806)------------------------------
% 1.41/0.55  % (5806)------------------------------
% 1.41/0.55  % (5805)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (5790)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.55  % (5803)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f172,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(subsumption_resolution,[],[f164,f78])).
% 1.41/0.55  fof(f78,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),X0),k7_relat_1(sK1,sK0))) )),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f12,f32,f47,f31])).
% 1.41/0.55  % (5784)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.55  % (5797)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (5802)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (5801)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 1.41/0.55    inference(equality_resolution,[],[f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,plain,(
% 1.41/0.55    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),sK0)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f13,f15])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,plain,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,plain,(
% 1.41/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.41/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.55  fof(f13,plain,(
% 1.41/0.55    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,plain,(
% 1.41/0.55    ? [X0,X1] : (~r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) & v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.41/0.55    inference(negated_conjecture,[],[f5])).
% 1.41/0.55  fof(f5,conjecture,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f12,f20])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,plain,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.41/0.55  fof(f12,plain,(
% 1.41/0.55    v1_relat_1(sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f8])).
% 1.41/0.55  fof(f164,plain,(
% 1.41/0.55    r2_hidden(k4_tarski(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),sK4(k7_relat_1(sK1,sK0),sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0))),k7_relat_1(sK1,sK0))),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f46,f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 1.41/0.55    inference(equality_resolution,[],[f17])).
% 1.41/0.55  fof(f17,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.41/0.55  fof(f46,plain,(
% 1.41/0.55    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0)),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f13,f14])).
% 1.41/0.55  fof(f14,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (5793)------------------------------
% 1.41/0.55  % (5793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (5793)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (5793)Memory used [KB]: 10874
% 1.41/0.55  % (5793)Time elapsed: 0.116 s
% 1.41/0.55  % (5793)------------------------------
% 1.41/0.55  % (5793)------------------------------
% 1.41/0.55  % (5811)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (5812)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (5783)Success in time 0.19 s
%------------------------------------------------------------------------------
