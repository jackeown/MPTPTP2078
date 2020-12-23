%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:27 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 105 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f64])).

fof(f64,plain,(
    sK1 != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f19,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f49,f23])).

fof(f23,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f49,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f42,f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) ) ),
    inference(forward_demodulation,[],[f41,f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f19,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f87,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f81,f23])).

fof(f81,plain,(
    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f23,f54])).

fof(f54,plain,(
    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f37,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X1,X0)) ) ),
    inference(forward_demodulation,[],[f39,f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f38,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(superposition,[],[f27,f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f37,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f36,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f36,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f35,f20])).

fof(f20,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f35,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f28,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (19192)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (19193)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (19191)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (19201)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (19200)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (19199)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (19199)Refutation not found, incomplete strategy% (19199)------------------------------
% 0.22/0.50  % (19199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19199)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19199)Memory used [KB]: 1535
% 0.22/0.50  % (19199)Time elapsed: 0.060 s
% 0.22/0.50  % (19199)------------------------------
% 0.22/0.50  % (19199)------------------------------
% 0.22/0.51  % (19201)Refutation not found, incomplete strategy% (19201)------------------------------
% 0.22/0.51  % (19201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19201)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19201)Memory used [KB]: 6140
% 0.22/0.51  % (19201)Time elapsed: 0.074 s
% 0.22/0.51  % (19201)------------------------------
% 0.22/0.51  % (19201)------------------------------
% 1.38/0.54  % (19186)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.38/0.54  % (19189)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.38/0.54  % (19187)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.55  % (19204)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.38/0.55  % (19205)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.38/0.55  % (19195)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.38/0.55  % (19202)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.38/0.55  % (19196)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.38/0.56  % (19194)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.38/0.56  % (19197)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.38/0.56  % (19203)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.38/0.56  % (19197)Refutation not found, incomplete strategy% (19197)------------------------------
% 1.38/0.56  % (19197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (19197)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (19197)Memory used [KB]: 10618
% 1.38/0.56  % (19197)Time elapsed: 0.124 s
% 1.38/0.56  % (19197)------------------------------
% 1.38/0.56  % (19197)------------------------------
% 1.38/0.56  % (19188)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.38/0.56  % (19189)Refutation not found, incomplete strategy% (19189)------------------------------
% 1.38/0.56  % (19189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (19189)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (19189)Memory used [KB]: 10618
% 1.38/0.56  % (19189)Time elapsed: 0.121 s
% 1.38/0.56  % (19189)------------------------------
% 1.38/0.56  % (19189)------------------------------
% 1.38/0.56  % (19203)Refutation found. Thanks to Tanya!
% 1.38/0.56  % SZS status Theorem for theBenchmark
% 1.38/0.56  % SZS output start Proof for theBenchmark
% 1.38/0.56  fof(f88,plain,(
% 1.38/0.56    $false),
% 1.38/0.56    inference(subsumption_resolution,[],[f87,f64])).
% 1.38/0.56  fof(f64,plain,(
% 1.38/0.56    sK1 != k3_xboole_0(sK0,sK1)),
% 1.38/0.56    inference(superposition,[],[f19,f50])).
% 1.38/0.56  fof(f50,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 1.38/0.56    inference(forward_demodulation,[],[f49,f23])).
% 1.38/0.56  fof(f23,plain,(
% 1.38/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.38/0.56    inference(cnf_transformation,[],[f7])).
% 1.38/0.56  fof(f7,axiom,(
% 1.38/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.38/0.56  fof(f49,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 1.38/0.56    inference(forward_demodulation,[],[f48,f26])).
% 1.38/0.56  fof(f26,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f9])).
% 1.38/0.56  fof(f9,axiom,(
% 1.38/0.56    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.38/0.56  fof(f48,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 1.38/0.56    inference(resolution,[],[f42,f21])).
% 1.38/0.56  fof(f21,plain,(
% 1.38/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f5])).
% 1.38/0.56  fof(f5,axiom,(
% 1.38/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.38/0.56  fof(f42,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)) )),
% 1.38/0.56    inference(forward_demodulation,[],[f41,f23])).
% 1.38/0.56  fof(f41,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1)))) )),
% 1.38/0.56    inference(resolution,[],[f24,f21])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f13])).
% 1.38/0.56  fof(f13,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.38/0.56  fof(f19,plain,(
% 1.38/0.56    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f12])).
% 1.38/0.56  fof(f12,plain,(
% 1.38/0.56    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f11])).
% 1.38/0.56  fof(f11,negated_conjecture,(
% 1.38/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 1.38/0.56    inference(negated_conjecture,[],[f10])).
% 1.38/0.56  fof(f10,conjecture,(
% 1.38/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 1.38/0.56  fof(f87,plain,(
% 1.38/0.56    sK1 = k3_xboole_0(sK0,sK1)),
% 1.38/0.56    inference(forward_demodulation,[],[f81,f23])).
% 1.38/0.56  fof(f81,plain,(
% 1.38/0.56    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK1))),
% 1.38/0.56    inference(superposition,[],[f23,f54])).
% 1.38/0.56  fof(f54,plain,(
% 1.38/0.56    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.38/0.56    inference(resolution,[],[f37,f40])).
% 1.38/0.56  fof(f40,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X1,X0))) )),
% 1.38/0.56    inference(forward_demodulation,[],[f39,f26])).
% 1.38/0.56  fof(f39,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f38,f21])).
% 1.38/0.56  fof(f38,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.38/0.56    inference(superposition,[],[f27,f23])).
% 1.38/0.56  fof(f27,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.38/0.56    inference(cnf_transformation,[],[f15])).
% 1.38/0.56  fof(f15,plain,(
% 1.38/0.56    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(flattening,[],[f14])).
% 1.38/0.56  fof(f14,plain,(
% 1.38/0.56    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f8])).
% 1.38/0.56  fof(f8,axiom,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.38/0.56  fof(f37,plain,(
% 1.38/0.56    r1_tarski(sK1,sK0)),
% 1.38/0.56    inference(resolution,[],[f36,f33])).
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.38/0.56    inference(equality_resolution,[],[f30])).
% 1.38/0.56  fof(f30,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.38/0.56    inference(cnf_transformation,[],[f2])).
% 1.38/0.56  fof(f2,axiom,(
% 1.38/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.38/0.56  fof(f36,plain,(
% 1.38/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.38/0.56    inference(subsumption_resolution,[],[f35,f20])).
% 1.38/0.56  fof(f20,plain,(
% 1.38/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f3])).
% 1.38/0.56  fof(f3,axiom,(
% 1.38/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.38/0.56    inference(resolution,[],[f28,f18])).
% 1.38/0.56  fof(f18,plain,(
% 1.38/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.38/0.56    inference(cnf_transformation,[],[f12])).
% 1.38/0.56  fof(f28,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f17,plain,(
% 1.38/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.38/0.56    inference(flattening,[],[f16])).
% 1.38/0.56  fof(f16,plain,(
% 1.38/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.38/0.56  % SZS output end Proof for theBenchmark
% 1.38/0.56  % (19203)------------------------------
% 1.38/0.56  % (19203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (19203)Termination reason: Refutation
% 1.38/0.56  
% 1.38/0.56  % (19203)Memory used [KB]: 1663
% 1.38/0.56  % (19203)Time elapsed: 0.083 s
% 1.38/0.56  % (19203)------------------------------
% 1.38/0.56  % (19203)------------------------------
% 1.38/0.56  % (19186)Refutation not found, incomplete strategy% (19186)------------------------------
% 1.38/0.56  % (19186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (19186)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (19186)Memory used [KB]: 6140
% 1.38/0.56  % (19186)Time elapsed: 0.121 s
% 1.38/0.56  % (19186)------------------------------
% 1.38/0.56  % (19186)------------------------------
% 1.38/0.56  % (19185)Success in time 0.19 s
%------------------------------------------------------------------------------
