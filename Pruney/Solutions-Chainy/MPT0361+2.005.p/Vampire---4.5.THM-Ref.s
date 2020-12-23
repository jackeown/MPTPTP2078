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
% DateTime   : Thu Dec  3 12:44:58 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 108 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  111 ( 221 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2563,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2555,f263])).

fof(f263,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2555,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f400,f2552])).

fof(f2552,plain,(
    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f2530,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2530,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f2528,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f2528,plain,(
    r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f2464,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f2464,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f2453,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2453,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),sK0) ),
    inference(superposition,[],[f1627,f89])).

fof(f89,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f78,f36])).

fof(f78,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f73,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f73,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f69,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f1627,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f537,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f537,plain,(
    ! [X17] : r1_tarski(k4_xboole_0(k2_xboole_0(sK2,X17),sK0),X17) ),
    inference(superposition,[],[f109,f85])).

fof(f85,plain,(
    sK0 = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f77,f36])).

fof(f77,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f70,f42])).

fof(f70,plain,(
    r1_tarski(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f68,f60])).

fof(f68,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f31,f41])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f109,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)),X1) ),
    inference(forward_demodulation,[],[f108,f53])).

fof(f108,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X0),X1) ),
    inference(unit_resulting_resolution,[],[f35,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f400,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f164,f378])).

fof(f378,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f31,f33,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f164,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f32,f150])).

fof(f150,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f33,f44])).

fof(f32,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 15:05:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (2364)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (2355)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (2343)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (2345)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (2347)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (2341)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (2357)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (2349)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (2342)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (2354)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (2365)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (2361)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (2346)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (2351)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (2363)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (2353)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (2359)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (2344)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (2356)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (2352)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (2348)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (2340)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % (2350)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (2360)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (2358)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (2362)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 2.13/0.67  % (2347)Refutation found. Thanks to Tanya!
% 2.13/0.67  % SZS status Theorem for theBenchmark
% 2.13/0.67  % SZS output start Proof for theBenchmark
% 2.13/0.67  fof(f2563,plain,(
% 2.13/0.67    $false),
% 2.13/0.67    inference(subsumption_resolution,[],[f2555,f263])).
% 2.13/0.67  fof(f263,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 2.13/0.67    inference(superposition,[],[f35,f53])).
% 2.13/0.67  fof(f53,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f7])).
% 2.13/0.67  fof(f7,axiom,(
% 2.13/0.67    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.13/0.67  fof(f35,plain,(
% 2.13/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f5])).
% 2.13/0.67  fof(f5,axiom,(
% 2.13/0.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.13/0.67  fof(f2555,plain,(
% 2.13/0.67    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.13/0.67    inference(backward_demodulation,[],[f400,f2552])).
% 2.13/0.67  fof(f2552,plain,(
% 2.13/0.67    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f2530,f44])).
% 2.13/0.67  fof(f44,plain,(
% 2.13/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f24])).
% 2.13/0.67  fof(f24,plain,(
% 2.13/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.67    inference(ennf_transformation,[],[f12])).
% 2.13/0.67  fof(f12,axiom,(
% 2.13/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.13/0.67  fof(f2530,plain,(
% 2.13/0.67    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f34,f2528,f40])).
% 2.13/0.67  fof(f40,plain,(
% 2.13/0.67    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f21])).
% 2.13/0.67  fof(f21,plain,(
% 2.13/0.67    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.13/0.67    inference(ennf_transformation,[],[f11])).
% 2.13/0.67  fof(f11,axiom,(
% 2.13/0.67    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.13/0.67  fof(f2528,plain,(
% 2.13/0.67    r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f2464,f61])).
% 2.13/0.67  fof(f61,plain,(
% 2.13/0.67    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.13/0.67    inference(equality_resolution,[],[f49])).
% 2.13/0.67  fof(f49,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.13/0.67    inference(cnf_transformation,[],[f10])).
% 2.13/0.67  fof(f10,axiom,(
% 2.13/0.67    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.13/0.67  fof(f2464,plain,(
% 2.13/0.67    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 2.13/0.67    inference(forward_demodulation,[],[f2453,f36])).
% 2.13/0.67  fof(f36,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f1])).
% 2.13/0.67  fof(f1,axiom,(
% 2.13/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.13/0.67  fof(f2453,plain,(
% 2.13/0.67    r1_tarski(k2_xboole_0(sK2,sK1),sK0)),
% 2.13/0.67    inference(superposition,[],[f1627,f89])).
% 2.13/0.67  fof(f89,plain,(
% 2.13/0.67    sK0 = k2_xboole_0(sK0,sK1)),
% 2.13/0.67    inference(superposition,[],[f78,f36])).
% 2.13/0.67  fof(f78,plain,(
% 2.13/0.67    sK0 = k2_xboole_0(sK1,sK0)),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f73,f42])).
% 2.13/0.67  fof(f42,plain,(
% 2.13/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.13/0.67    inference(cnf_transformation,[],[f22])).
% 2.13/0.67  fof(f22,plain,(
% 2.13/0.67    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.13/0.67    inference(ennf_transformation,[],[f4])).
% 2.13/0.67  fof(f4,axiom,(
% 2.13/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.13/0.67  fof(f73,plain,(
% 2.13/0.67    r1_tarski(sK1,sK0)),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f69,f60])).
% 2.13/0.67  fof(f60,plain,(
% 2.13/0.67    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.13/0.67    inference(equality_resolution,[],[f50])).
% 2.13/0.67  fof(f50,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.13/0.67    inference(cnf_transformation,[],[f10])).
% 2.13/0.67  fof(f69,plain,(
% 2.13/0.67    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f34,f33,f41])).
% 2.13/0.67  fof(f41,plain,(
% 2.13/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f21])).
% 2.13/0.67  fof(f33,plain,(
% 2.13/0.67    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.13/0.67    inference(cnf_transformation,[],[f20])).
% 2.13/0.67  fof(f20,plain,(
% 2.13/0.67    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.67    inference(ennf_transformation,[],[f18])).
% 2.13/0.67  fof(f18,negated_conjecture,(
% 2.13/0.67    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.13/0.67    inference(negated_conjecture,[],[f17])).
% 2.13/0.67  fof(f17,conjecture,(
% 2.13/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 2.13/0.67  fof(f1627,plain,(
% 2.13/0.67    ( ! [X0] : (r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK0,X0))) )),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f537,f56])).
% 2.13/0.67  fof(f56,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f28])).
% 2.13/0.67  fof(f28,plain,(
% 2.13/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.67    inference(ennf_transformation,[],[f9])).
% 2.13/0.67  fof(f9,axiom,(
% 2.13/0.67    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.13/0.67  fof(f537,plain,(
% 2.13/0.67    ( ! [X17] : (r1_tarski(k4_xboole_0(k2_xboole_0(sK2,X17),sK0),X17)) )),
% 2.13/0.67    inference(superposition,[],[f109,f85])).
% 2.13/0.67  fof(f85,plain,(
% 2.13/0.67    sK0 = k2_xboole_0(sK0,sK2)),
% 2.13/0.67    inference(superposition,[],[f77,f36])).
% 2.13/0.67  fof(f77,plain,(
% 2.13/0.67    sK0 = k2_xboole_0(sK2,sK0)),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f70,f42])).
% 2.13/0.67  fof(f70,plain,(
% 2.13/0.67    r1_tarski(sK2,sK0)),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f68,f60])).
% 2.13/0.67  fof(f68,plain,(
% 2.13/0.67    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f34,f31,f41])).
% 2.13/0.67  fof(f31,plain,(
% 2.13/0.67    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.13/0.67    inference(cnf_transformation,[],[f20])).
% 2.13/0.67  fof(f109,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)),X1)) )),
% 2.13/0.67    inference(forward_demodulation,[],[f108,f53])).
% 2.13/0.67  fof(f108,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X0),X1)) )),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f35,f54])).
% 2.13/0.67  fof(f54,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f26])).
% 2.13/0.67  fof(f26,plain,(
% 2.13/0.67    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.67    inference(ennf_transformation,[],[f8])).
% 2.13/0.67  fof(f8,axiom,(
% 2.13/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.13/0.67  fof(f34,plain,(
% 2.13/0.67    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f14])).
% 2.13/0.67  fof(f14,axiom,(
% 2.13/0.67    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.13/0.67  fof(f400,plain,(
% 2.13/0.67    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.13/0.67    inference(backward_demodulation,[],[f164,f378])).
% 2.13/0.67  fof(f378,plain,(
% 2.13/0.67    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f31,f33,f57])).
% 2.13/0.67  fof(f57,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f30])).
% 2.13/0.67  fof(f30,plain,(
% 2.13/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.67    inference(flattening,[],[f29])).
% 2.13/0.67  fof(f29,plain,(
% 2.13/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.13/0.67    inference(ennf_transformation,[],[f16])).
% 2.13/0.67  fof(f16,axiom,(
% 2.13/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.13/0.67  fof(f164,plain,(
% 2.13/0.67    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.13/0.67    inference(backward_demodulation,[],[f32,f150])).
% 2.13/0.67  fof(f150,plain,(
% 2.13/0.67    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f33,f44])).
% 2.13/0.67  fof(f32,plain,(
% 2.13/0.67    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 2.13/0.67    inference(cnf_transformation,[],[f20])).
% 2.13/0.67  % SZS output end Proof for theBenchmark
% 2.13/0.67  % (2347)------------------------------
% 2.13/0.67  % (2347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.67  % (2347)Termination reason: Refutation
% 2.13/0.67  
% 2.13/0.67  % (2347)Memory used [KB]: 3198
% 2.13/0.67  % (2347)Time elapsed: 0.214 s
% 2.13/0.67  % (2347)------------------------------
% 2.13/0.67  % (2347)------------------------------
% 2.13/0.68  % (2339)Success in time 0.313 s
%------------------------------------------------------------------------------
