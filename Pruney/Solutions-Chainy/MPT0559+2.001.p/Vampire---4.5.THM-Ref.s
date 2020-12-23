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
% DateTime   : Thu Dec  3 12:49:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  81 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 162 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(resolution,[],[f67,f19])).

fof(f19,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_relat_1)).

fof(f67,plain,(
    ! [X2,X3] : r1_tarski(k9_relat_1(k7_relat_1(sK2,X3),X2),k9_relat_1(sK2,X2)) ),
    inference(forward_demodulation,[],[f66,f30])).

fof(f30,plain,(
    ! [X2,X3] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3)) = k9_relat_1(k7_relat_1(sK2,X2),X3) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X3] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)),k9_relat_1(sK2,X2)) ),
    inference(forward_demodulation,[],[f65,f27])).

fof(f27,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(sK2,X1)) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f18,f22])).

fof(f65,plain,(
    ! [X2,X3] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)),k2_relat_1(k7_relat_1(sK2,X2))) ),
    inference(subsumption_resolution,[],[f64,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(resolution,[],[f26,f23])).

fof(f64,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2))
      | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)),k2_relat_1(k7_relat_1(sK2,X2))) ) ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f60,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X2))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2))
      | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)),k2_relat_1(k7_relat_1(sK2,X2))) ) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f41,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3)) ),
    inference(subsumption_resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X2))
      | r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3)) ) ),
    inference(subsumption_resolution,[],[f34,f18])).

fof(f34,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(k7_relat_1(sK2,X2))
      | r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f28,plain,(
    ! [X2] : r1_tarski(k7_relat_1(sK2,X2),sK2) ),
    inference(resolution,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (12424)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (12419)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (12419)Refutation not found, incomplete strategy% (12419)------------------------------
% 0.22/0.51  % (12419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12419)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12419)Memory used [KB]: 10490
% 0.22/0.51  % (12419)Time elapsed: 0.090 s
% 0.22/0.51  % (12419)------------------------------
% 0.22/0.51  % (12419)------------------------------
% 0.22/0.51  % (12418)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (12417)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (12423)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12423)Refutation not found, incomplete strategy% (12423)------------------------------
% 0.22/0.52  % (12423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12423)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12423)Memory used [KB]: 6140
% 0.22/0.52  % (12423)Time elapsed: 0.100 s
% 0.22/0.52  % (12423)------------------------------
% 0.22/0.52  % (12423)------------------------------
% 0.22/0.52  % (12435)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (12433)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (12428)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (12429)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (12439)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.53  % (12426)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (12430)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.53  % (12437)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.53  % (12426)Refutation not found, incomplete strategy% (12426)------------------------------
% 0.22/0.53  % (12426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12426)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12426)Memory used [KB]: 10490
% 0.22/0.53  % (12426)Time elapsed: 0.114 s
% 0.22/0.53  % (12426)------------------------------
% 0.22/0.53  % (12426)------------------------------
% 0.22/0.53  % (12420)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.53  % (12416)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.53  % (12437)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(resolution,[],[f67,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_relat_1)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X3),X2),k9_relat_1(sK2,X2))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f66,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3)) = k9_relat_1(k7_relat_1(sK2,X2),X3)) )),
% 0.22/0.53    inference(resolution,[],[f26,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.22/0.53    inference(resolution,[],[f18,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    v1_relat_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)),k9_relat_1(sK2,X2))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f65,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X1] : (k2_relat_1(k7_relat_1(sK2,X1)) = k9_relat_1(sK2,X1)) )),
% 0.22/0.53    inference(resolution,[],[f18,f22])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)),k2_relat_1(k7_relat_1(sK2,X2)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f64,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 0.22/0.53    inference(resolution,[],[f26,f23])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)) | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)),k2_relat_1(k7_relat_1(sK2,X2)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f60,f26])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK2,X2)) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)) | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)),k2_relat_1(k7_relat_1(sK2,X2)))) )),
% 0.22/0.53    inference(resolution,[],[f41,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f40,f26])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK2,X2)) | r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f34,f18])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,X2)) | r1_tarski(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(sK2,X3))) )),
% 0.22/0.53    inference(resolution,[],[f28,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X2] : (r1_tarski(k7_relat_1(sK2,X2),sK2)) )),
% 0.22/0.53    inference(resolution,[],[f18,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (12437)------------------------------
% 0.22/0.53  % (12437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12437)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (12437)Memory used [KB]: 6140
% 0.22/0.53  % (12437)Time elapsed: 0.115 s
% 0.22/0.53  % (12437)------------------------------
% 0.22/0.53  % (12437)------------------------------
% 0.22/0.53  % (12414)Success in time 0.165 s
%------------------------------------------------------------------------------
