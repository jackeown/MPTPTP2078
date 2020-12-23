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
% DateTime   : Thu Dec  3 13:19:55 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   43 (  76 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 248 expanded)
%              Number of equality atoms :   28 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1962,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f53,f1769,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1769,plain,(
    ! [X0] : r2_hidden(sK4(k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f1508,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1508,plain,(
    ! [X0] : r2_hidden(sK4(k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f95,f1490])).

fof(f1490,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f25,f24,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f49,f93])).

fof(f93,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(forward_demodulation,[],[f92,f64])).

fof(f64,plain,(
    sK1 = k6_domain_1(sK1,sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f23,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f23,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f22,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f63,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f63,plain,(
    m1_subset_1(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f22,f23,f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    ! [X0] : r2_hidden(sK4(sK0),k2_xboole_0(X0,sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f65,plain,(
    r2_hidden(sK4(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f26,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (23934)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (23927)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (23934)Refutation not found, incomplete strategy% (23934)------------------------------
% 0.22/0.51  % (23934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23934)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23934)Memory used [KB]: 10618
% 0.22/0.51  % (23934)Time elapsed: 0.104 s
% 0.22/0.51  % (23934)------------------------------
% 0.22/0.51  % (23934)------------------------------
% 0.22/0.51  % (23937)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (23930)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (23928)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (23942)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (23933)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (23945)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.52  % (23945)Refutation not found, incomplete strategy% (23945)------------------------------
% 1.26/0.52  % (23945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (23945)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (23945)Memory used [KB]: 10746
% 1.26/0.53  % (23945)Time elapsed: 0.069 s
% 1.26/0.53  % (23945)------------------------------
% 1.26/0.53  % (23945)------------------------------
% 1.26/0.53  % (23947)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.26/0.54  % (23929)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.54  % (23925)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.54  % (23924)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.54  % (23925)Refutation not found, incomplete strategy% (23925)------------------------------
% 1.26/0.54  % (23925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (23925)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (23925)Memory used [KB]: 10746
% 1.26/0.54  % (23925)Time elapsed: 0.124 s
% 1.26/0.54  % (23925)------------------------------
% 1.26/0.54  % (23925)------------------------------
% 1.26/0.54  % (23926)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.54  % (23948)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (23933)Refutation not found, incomplete strategy% (23933)------------------------------
% 1.36/0.54  % (23933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (23933)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (23933)Memory used [KB]: 10618
% 1.36/0.54  % (23933)Time elapsed: 0.137 s
% 1.36/0.54  % (23933)------------------------------
% 1.36/0.54  % (23933)------------------------------
% 1.36/0.54  % (23952)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (23953)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (23923)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.55  % (23950)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.55  % (23939)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.55  % (23940)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (23931)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (23943)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.55  % (23944)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (23932)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (23941)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % (23949)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.56  % (23938)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.56  % (23935)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.56  % (23936)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.57  % (23946)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.57  % (23927)Refutation found. Thanks to Tanya!
% 1.36/0.57  % SZS status Theorem for theBenchmark
% 1.36/0.57  % SZS output start Proof for theBenchmark
% 1.36/0.57  fof(f1962,plain,(
% 1.36/0.57    $false),
% 1.36/0.57    inference(unit_resulting_resolution,[],[f53,f1769,f30])).
% 1.36/0.57  fof(f30,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f16])).
% 1.36/0.57  fof(f16,plain,(
% 1.36/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f9])).
% 1.36/0.57  fof(f9,axiom,(
% 1.36/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.36/0.57  fof(f1769,plain,(
% 1.36/0.57    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0),X0)) )),
% 1.36/0.57    inference(forward_demodulation,[],[f1508,f48])).
% 1.36/0.57  fof(f48,plain,(
% 1.36/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.57    inference(cnf_transformation,[],[f7])).
% 1.36/0.57  fof(f7,axiom,(
% 1.36/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.36/0.57  fof(f1508,plain,(
% 1.36/0.57    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0),k2_xboole_0(X0,k1_xboole_0))) )),
% 1.36/0.57    inference(backward_demodulation,[],[f95,f1490])).
% 1.36/0.57  fof(f1490,plain,(
% 1.36/0.57    k1_xboole_0 = sK0),
% 1.36/0.57    inference(unit_resulting_resolution,[],[f25,f24,f153])).
% 1.36/0.57  fof(f153,plain,(
% 1.36/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) )),
% 1.36/0.57    inference(superposition,[],[f49,f93])).
% 1.36/0.57  fof(f93,plain,(
% 1.36/0.57    sK1 = k1_tarski(sK3(sK1))),
% 1.36/0.57    inference(forward_demodulation,[],[f92,f64])).
% 1.36/0.57  fof(f64,plain,(
% 1.36/0.57    sK1 = k6_domain_1(sK1,sK3(sK1))),
% 1.36/0.57    inference(unit_resulting_resolution,[],[f22,f23,f36])).
% 1.36/0.57  fof(f36,plain,(
% 1.36/0.57    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f19])).
% 1.36/0.58  fof(f19,plain,(
% 1.36/0.58    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.36/0.58    inference(ennf_transformation,[],[f11])).
% 1.36/0.58  fof(f11,axiom,(
% 1.36/0.58    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.36/0.58  fof(f23,plain,(
% 1.36/0.58    v1_zfmisc_1(sK1)),
% 1.36/0.58    inference(cnf_transformation,[],[f15])).
% 1.36/0.58  fof(f15,plain,(
% 1.36/0.58    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.36/0.58    inference(flattening,[],[f14])).
% 1.36/0.58  fof(f14,plain,(
% 1.36/0.58    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.36/0.58    inference(ennf_transformation,[],[f13])).
% 1.36/0.58  fof(f13,negated_conjecture,(
% 1.36/0.58    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.36/0.58    inference(negated_conjecture,[],[f12])).
% 1.36/0.58  fof(f12,conjecture,(
% 1.36/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.36/0.58  fof(f22,plain,(
% 1.36/0.58    ~v1_xboole_0(sK1)),
% 1.36/0.58    inference(cnf_transformation,[],[f15])).
% 1.36/0.58  fof(f92,plain,(
% 1.36/0.58    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1))),
% 1.36/0.58    inference(unit_resulting_resolution,[],[f22,f63,f38])).
% 1.36/0.58  fof(f38,plain,(
% 1.36/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f21])).
% 1.36/0.58  fof(f21,plain,(
% 1.36/0.58    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.36/0.58    inference(flattening,[],[f20])).
% 1.36/0.58  fof(f20,plain,(
% 1.36/0.58    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.36/0.58    inference(ennf_transformation,[],[f10])).
% 1.36/0.58  fof(f10,axiom,(
% 1.36/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.36/0.58  fof(f63,plain,(
% 1.36/0.58    m1_subset_1(sK3(sK1),sK1)),
% 1.36/0.58    inference(unit_resulting_resolution,[],[f22,f23,f35])).
% 1.36/0.58  fof(f35,plain,(
% 1.36/0.58    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f19])).
% 1.36/0.58  fof(f49,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 1.36/0.58    inference(cnf_transformation,[],[f8])).
% 1.36/0.58  fof(f8,axiom,(
% 1.36/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.36/0.58  fof(f24,plain,(
% 1.36/0.58    r1_tarski(sK0,sK1)),
% 1.36/0.58    inference(cnf_transformation,[],[f15])).
% 1.36/0.58  fof(f25,plain,(
% 1.36/0.58    sK0 != sK1),
% 1.36/0.58    inference(cnf_transformation,[],[f15])).
% 1.36/0.58  fof(f95,plain,(
% 1.36/0.58    ( ! [X0] : (r2_hidden(sK4(sK0),k2_xboole_0(X0,sK0))) )),
% 1.36/0.58    inference(unit_resulting_resolution,[],[f65,f54])).
% 1.36/0.58  fof(f54,plain,(
% 1.36/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.36/0.58    inference(equality_resolution,[],[f46])).
% 1.36/0.58  fof(f46,plain,(
% 1.36/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.36/0.58    inference(cnf_transformation,[],[f4])).
% 1.36/0.58  fof(f4,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.36/0.58  fof(f65,plain,(
% 1.36/0.58    r2_hidden(sK4(sK0),sK0)),
% 1.36/0.58    inference(unit_resulting_resolution,[],[f26,f39])).
% 1.36/0.58  fof(f39,plain,(
% 1.36/0.58    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f2])).
% 1.36/0.58  fof(f2,axiom,(
% 1.36/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.58  fof(f26,plain,(
% 1.36/0.58    ~v1_xboole_0(sK0)),
% 1.36/0.58    inference(cnf_transformation,[],[f15])).
% 1.36/0.58  fof(f53,plain,(
% 1.36/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.58    inference(equality_resolution,[],[f27])).
% 1.36/0.58  fof(f27,plain,(
% 1.36/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.36/0.58    inference(cnf_transformation,[],[f5])).
% 1.36/0.58  fof(f5,axiom,(
% 1.36/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.58  % SZS output end Proof for theBenchmark
% 1.36/0.58  % (23927)------------------------------
% 1.36/0.58  % (23927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (23927)Termination reason: Refutation
% 1.36/0.58  
% 1.36/0.58  % (23927)Memory used [KB]: 6780
% 1.36/0.58  % (23927)Time elapsed: 0.165 s
% 1.36/0.58  % (23927)------------------------------
% 1.36/0.58  % (23927)------------------------------
% 1.36/0.58  % (23920)Success in time 0.214 s
%------------------------------------------------------------------------------
