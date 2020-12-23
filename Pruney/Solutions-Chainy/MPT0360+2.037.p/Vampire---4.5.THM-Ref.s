%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 146 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 432 expanded)
%              Number of equality atoms :   14 (  47 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f863,plain,(
    $false ),
    inference(global_subsumption,[],[f819,f860])).

fof(f860,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f18,f818,f520])).

fof(f520,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f515])).

fof(f515,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f316,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f316,plain,(
    ! [X6,X8,X7,X5] :
      ( r2_hidden(sK3(X5,X7),X8)
      | r1_tarski(X5,X7)
      | ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X8) ) ),
    inference(resolution,[],[f91,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK3(X6,X7),X8)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f818,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f17,f19,f790,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f790,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f770,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f21,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f25,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f21,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f770,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f18,f64,f520])).

fof(f64,plain,(
    r1_tarski(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f17,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

% (20168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f819,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f790,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f28,f22])).

fof(f22,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (20146)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (20146)Refutation not found, incomplete strategy% (20146)------------------------------
% 0.21/0.55  % (20146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20146)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20146)Memory used [KB]: 1663
% 0.21/0.55  % (20146)Time elapsed: 0.121 s
% 0.21/0.55  % (20146)------------------------------
% 0.21/0.55  % (20146)------------------------------
% 0.21/0.56  % (20170)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (20164)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (20154)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % (20172)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (20156)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (20154)Refutation not found, incomplete strategy% (20154)------------------------------
% 0.21/0.57  % (20154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20154)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20154)Memory used [KB]: 10618
% 0.21/0.57  % (20154)Time elapsed: 0.138 s
% 0.21/0.57  % (20154)------------------------------
% 0.21/0.57  % (20154)------------------------------
% 0.21/0.57  % (20152)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (20151)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (20158)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (20156)Refutation not found, incomplete strategy% (20156)------------------------------
% 0.21/0.58  % (20156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (20161)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (20156)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (20156)Memory used [KB]: 10618
% 0.21/0.58  % (20156)Time elapsed: 0.149 s
% 0.21/0.58  % (20156)------------------------------
% 0.21/0.58  % (20156)------------------------------
% 0.21/0.58  % (20149)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.59  % (20148)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (20148)Refutation not found, incomplete strategy% (20148)------------------------------
% 0.21/0.59  % (20148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (20148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (20148)Memory used [KB]: 10618
% 0.21/0.59  % (20148)Time elapsed: 0.160 s
% 0.21/0.59  % (20148)------------------------------
% 0.21/0.59  % (20148)------------------------------
% 0.21/0.60  % (20150)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.60  % (20175)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.60  % (20173)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.60  % (20170)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % (20169)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.60  % (20162)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.60  % (20165)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.61  % (20147)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.61  % (20167)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.61  % SZS output start Proof for theBenchmark
% 0.21/0.61  fof(f863,plain,(
% 0.21/0.61    $false),
% 0.21/0.61    inference(global_subsumption,[],[f819,f860])).
% 0.21/0.61  fof(f860,plain,(
% 0.21/0.61    r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f18,f818,f520])).
% 0.21/0.61  fof(f520,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(duplicate_literal_removal,[],[f515])).
% 0.21/0.61  fof(f515,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(resolution,[],[f316,f32])).
% 0.21/0.61  fof(f32,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f16])).
% 0.21/0.61  fof(f16,plain,(
% 0.21/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.61    inference(ennf_transformation,[],[f1])).
% 0.21/0.61  fof(f1,axiom,(
% 0.21/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.61  fof(f316,plain,(
% 0.21/0.61    ( ! [X6,X8,X7,X5] : (r2_hidden(sK3(X5,X7),X8) | r1_tarski(X5,X7) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,X8)) )),
% 0.21/0.61    inference(resolution,[],[f91,f30])).
% 0.21/0.61  fof(f30,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f16])).
% 0.21/0.61  fof(f91,plain,(
% 0.21/0.61    ( ! [X6,X8,X7] : (r2_hidden(sK3(X6,X7),X8) | ~r1_tarski(X6,X8) | r1_tarski(X6,X7)) )),
% 0.21/0.61    inference(resolution,[],[f30,f31])).
% 0.21/0.61  fof(f31,plain,(
% 0.21/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f16])).
% 0.21/0.61  fof(f818,plain,(
% 0.21/0.61    r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f17,f19,f790,f29])).
% 0.21/0.61  fof(f29,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f15])).
% 0.21/0.61  fof(f15,plain,(
% 0.21/0.61    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.61    inference(flattening,[],[f14])).
% 0.21/0.61  fof(f14,plain,(
% 0.21/0.61    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.61    inference(ennf_transformation,[],[f6])).
% 0.21/0.61  fof(f6,axiom,(
% 0.21/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 0.21/0.61  fof(f790,plain,(
% 0.21/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f770,f49])).
% 0.21/0.61  fof(f49,plain,(
% 0.21/0.61    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 0.21/0.61    inference(global_subsumption,[],[f21,f48])).
% 0.21/0.61  fof(f48,plain,(
% 0.21/0.61    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 0.21/0.61    inference(resolution,[],[f25,f41])).
% 0.21/0.61  fof(f41,plain,(
% 0.21/0.61    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.21/0.61    inference(equality_resolution,[],[f33])).
% 0.21/0.61  fof(f33,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.61    inference(cnf_transformation,[],[f2])).
% 0.21/0.61  fof(f2,axiom,(
% 0.21/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.61  fof(f25,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f12])).
% 0.21/0.61  fof(f12,plain,(
% 0.21/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.61    inference(ennf_transformation,[],[f3])).
% 0.21/0.61  fof(f3,axiom,(
% 0.21/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.61  fof(f21,plain,(
% 0.21/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f5])).
% 0.21/0.61  fof(f5,axiom,(
% 0.21/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.61  fof(f770,plain,(
% 0.21/0.61    r1_tarski(sK1,sK0)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f18,f64,f520])).
% 0.21/0.61  fof(f64,plain,(
% 0.21/0.61    r1_tarski(sK2,sK0)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f59,f40])).
% 0.21/0.61  fof(f40,plain,(
% 0.21/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.61    inference(equality_resolution,[],[f34])).
% 0.21/0.61  fof(f34,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.61    inference(cnf_transformation,[],[f2])).
% 0.21/0.61  fof(f59,plain,(
% 0.21/0.61    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f21,f17,f26])).
% 0.21/0.61  fof(f26,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f12])).
% 0.21/0.61  fof(f19,plain,(
% 0.21/0.61    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.61    inference(cnf_transformation,[],[f11])).
% 0.21/0.61  fof(f11,plain,(
% 0.21/0.61    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.61    inference(flattening,[],[f10])).
% 0.21/0.61  fof(f10,plain,(
% 0.21/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.61    inference(ennf_transformation,[],[f9])).
% 0.21/0.61  fof(f9,negated_conjecture,(
% 0.21/0.61    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.61    inference(negated_conjecture,[],[f8])).
% 0.21/0.61  fof(f8,conjecture,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 0.21/0.61  fof(f17,plain,(
% 0.21/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.61    inference(cnf_transformation,[],[f11])).
% 0.21/0.61  fof(f18,plain,(
% 0.21/0.61    r1_tarski(sK1,sK2)),
% 0.21/0.61    inference(cnf_transformation,[],[f11])).
% 0.21/0.61  % (20168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.61  fof(f819,plain,(
% 0.21/0.61    ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f20,f790,f37])).
% 0.21/0.61  fof(f37,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.61    inference(definition_unfolding,[],[f28,f22])).
% 0.21/0.61  fof(f22,plain,(
% 0.21/0.61    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.21/0.61    inference(cnf_transformation,[],[f4])).
% 0.21/0.61  fof(f4,axiom,(
% 0.21/0.61    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.61  fof(f28,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f13])).
% 0.21/0.61  fof(f13,plain,(
% 0.21/0.61    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.61    inference(ennf_transformation,[],[f7])).
% 0.21/0.61  fof(f7,axiom,(
% 0.21/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.61  fof(f20,plain,(
% 0.21/0.61    k1_xboole_0 != sK1),
% 0.21/0.61    inference(cnf_transformation,[],[f11])).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 0.21/0.61  % (20170)------------------------------
% 0.21/0.61  % (20170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (20170)Termination reason: Refutation
% 0.21/0.61  
% 0.21/0.61  % (20170)Memory used [KB]: 6908
% 0.21/0.61  % (20170)Time elapsed: 0.173 s
% 0.21/0.61  % (20170)------------------------------
% 0.21/0.61  % (20170)------------------------------
% 0.21/0.61  % (20145)Success in time 0.251 s
%------------------------------------------------------------------------------
