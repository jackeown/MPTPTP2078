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
% DateTime   : Thu Dec  3 12:56:23 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  92 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 ( 172 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1220,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1209,f152])).

fof(f152,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,k1_relat_1(sK2)),k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f64,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k1_relat_1(sK2),X0),k2_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f52,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f51,f42])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f41,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

fof(f51,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f39,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f23,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1209,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,k1_relat_1(sK2)),k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f413,f60])).

fof(f60,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_relat_1(sK2),X2)
      | ~ r1_tarski(X2,k2_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f49,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f49,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k3_relat_1(sK2),X0),k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f24,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f24,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f413,plain,(
    r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK1,k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f406,f42])).

fof(f406,plain,
    ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f164,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f164,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,k2_relat_1(sK2)),k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f67,f29])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),k2_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f54,f26])).

fof(f54,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f53,f42])).

fof(f53,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f40,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:51:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.48  % (25568)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.23/0.49  % (25577)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.23/0.50  % (25590)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.23/0.50  % (25574)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.23/0.50  % (25585)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.51  % (25573)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.23/0.51  % (25572)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.51  % (25587)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.23/0.51  % (25583)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.23/0.51  % (25591)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.23/0.51  % (25569)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.23/0.51  % (25570)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.23/0.51  % (25589)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.23/0.52  % (25586)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.23/0.52  % (25575)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (25576)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.23/0.52  % (25579)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.23/0.52  % (25578)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.23/0.52  % (25582)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.23/0.53  % (25571)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.23/0.53  % (25584)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.23/0.53  % (25571)Refutation not found, incomplete strategy% (25571)------------------------------
% 0.23/0.53  % (25571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (25571)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (25571)Memory used [KB]: 10490
% 0.23/0.53  % (25571)Time elapsed: 0.105 s
% 0.23/0.53  % (25571)------------------------------
% 0.23/0.53  % (25571)------------------------------
% 0.23/0.53  % (25590)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.54  % (25581)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.23/0.54  % (25588)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f1220,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(subsumption_resolution,[],[f1209,f152])).
% 0.23/0.54  fof(f152,plain,(
% 0.23/0.54    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,k1_relat_1(sK2)),k2_xboole_0(sK0,X0))) )),
% 0.23/0.54    inference(superposition,[],[f64,f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.23/0.54  fof(f64,plain,(
% 0.23/0.54    ( ! [X0] : (r1_tarski(k2_xboole_0(k1_relat_1(sK2),X0),k2_xboole_0(sK0,X0))) )),
% 0.23/0.54    inference(resolution,[],[f52,f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f16])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f5])).
% 0.23/0.54  fof(f5,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.23/0.54  fof(f52,plain,(
% 0.23/0.54    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.23/0.54    inference(subsumption_resolution,[],[f51,f42])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    v1_relat_1(sK2)),
% 0.23/0.54    inference(subsumption_resolution,[],[f41,f34])).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,axiom,(
% 0.23/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.23/0.54  fof(f41,plain,(
% 0.23/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.23/0.54    inference(resolution,[],[f23,f33])).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f14,plain,(
% 0.23/0.54    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.54    inference(ennf_transformation,[],[f13])).
% 0.23/0.54  fof(f13,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.23/0.54    inference(negated_conjecture,[],[f12])).
% 0.23/0.54  fof(f12,conjecture,(
% 0.23/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).
% 0.23/0.54  fof(f51,plain,(
% 0.23/0.54    ~v1_relat_1(sK2) | r1_tarski(k1_relat_1(sK2),sK0)),
% 0.23/0.54    inference(resolution,[],[f39,f38])).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,axiom,(
% 0.23/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    v4_relat_1(sK2,sK0)),
% 0.23/0.54    inference(resolution,[],[f23,f31])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.54    inference(ennf_transformation,[],[f11])).
% 0.23/0.54  fof(f11,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.54  fof(f1209,plain,(
% 0.23/0.54    ~r1_tarski(k2_xboole_0(sK1,k1_relat_1(sK2)),k2_xboole_0(sK0,sK1))),
% 0.23/0.54    inference(resolution,[],[f413,f60])).
% 0.23/0.54  fof(f60,plain,(
% 0.23/0.54    ( ! [X2] : (~r1_tarski(k3_relat_1(sK2),X2) | ~r1_tarski(X2,k2_xboole_0(sK0,sK1))) )),
% 0.23/0.54    inference(superposition,[],[f49,f27])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.23/0.54  fof(f49,plain,(
% 0.23/0.54    ( ! [X0] : (~r1_tarski(k2_xboole_0(k3_relat_1(sK2),X0),k2_xboole_0(sK0,sK1))) )),
% 0.23/0.54    inference(resolution,[],[f24,f25])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.23/0.54    inference(ennf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f413,plain,(
% 0.23/0.54    r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK1,k1_relat_1(sK2)))),
% 0.23/0.54    inference(subsumption_resolution,[],[f406,f42])).
% 0.23/0.54  fof(f406,plain,(
% 0.23/0.54    r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK1,k1_relat_1(sK2))) | ~v1_relat_1(sK2)),
% 0.23/0.54    inference(superposition,[],[f164,f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f9])).
% 0.23/0.54  fof(f9,axiom,(
% 0.23/0.54    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.23/0.54  fof(f164,plain,(
% 0.23/0.54    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,k2_relat_1(sK2)),k2_xboole_0(sK1,X0))) )),
% 0.23/0.54    inference(superposition,[],[f67,f29])).
% 0.23/0.54  fof(f67,plain,(
% 0.23/0.54    ( ! [X0] : (r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),k2_xboole_0(sK1,X0))) )),
% 0.23/0.54    inference(resolution,[],[f54,f26])).
% 0.23/0.54  fof(f54,plain,(
% 0.23/0.54    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f53,f42])).
% 0.23/0.54  fof(f53,plain,(
% 0.23/0.54    ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),sK1)),
% 0.23/0.54    inference(resolution,[],[f40,f36])).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,axiom,(
% 0.23/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    v5_relat_1(sK2,sK1)),
% 0.23/0.54    inference(resolution,[],[f23,f32])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f19])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (25590)------------------------------
% 0.23/0.54  % (25590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (25590)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (25590)Memory used [KB]: 2174
% 0.23/0.54  % (25590)Time elapsed: 0.096 s
% 0.23/0.54  % (25590)------------------------------
% 0.23/0.54  % (25590)------------------------------
% 0.23/0.54  % (25567)Success in time 0.176 s
%------------------------------------------------------------------------------
