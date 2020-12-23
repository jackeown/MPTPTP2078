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
% DateTime   : Thu Dec  3 12:56:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 152 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  134 ( 408 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f88,f53])).

fof(f53,plain,(
    v4_relat_1(sK4,sK1) ),
    inference(resolution,[],[f52,f21])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X0,X1) )
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | v4_relat_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f50,f38])).

fof(f38,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ v1_relat_1(sK4)
      | v4_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f49,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK4),X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f30,f48])).

fof(f48,plain,(
    sK0 = k2_xboole_0(k1_relat_1(sK4),sK0) ),
    inference(subsumption_resolution,[],[f47,f38])).

fof(f47,plain,
    ( ~ v1_relat_1(sK4)
    | sK0 = k2_xboole_0(k1_relat_1(sK4),sK0) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    v4_relat_1(sK4,sK0) ),
    inference(resolution,[],[f32,f20])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f40,plain,(
    ! [X2,X3] :
      ( ~ v4_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | k2_xboole_0(k1_relat_1(X2),X3) = X3 ) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f88,plain,(
    ~ v4_relat_1(sK4,sK1) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v4_relat_1(sK4,sK1) ),
    inference(resolution,[],[f84,f25])).

fof(f84,plain,(
    ~ r1_tarski(k1_relat_1(sK4),sK1) ),
    inference(subsumption_resolution,[],[f83,f67])).

fof(f67,plain,(
    v5_relat_1(sK4,sK3) ),
    inference(resolution,[],[f66,f22])).

fof(f22,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | v5_relat_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f64,f38])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | ~ v1_relat_1(sK4)
      | v5_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f63,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK4),X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f30,f62])).

fof(f62,plain,(
    sK2 = k2_xboole_0(k2_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f61,f38])).

fof(f61,plain,
    ( ~ v1_relat_1(sK4)
    | sK2 = k2_xboole_0(k2_relat_1(sK4),sK2) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f33,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X3] :
      ( ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | k2_xboole_0(k2_relat_1(X2),X3) = X3 ) ),
    inference(resolution,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v5_relat_1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f80,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4)
    | ~ v5_relat_1(sK4,sK3) ),
    inference(resolution,[],[f79,f27])).

fof(f79,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK1) ),
    inference(subsumption_resolution,[],[f75,f38])).

fof(f75,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f29,f23])).

fof(f23,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:29:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (2022)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (2037)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (2024)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (2028)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (2040)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (2023)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (2025)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (2030)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (2025)Refutation not found, incomplete strategy% (2025)------------------------------
% 0.22/0.52  % (2025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2025)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2025)Memory used [KB]: 10490
% 0.22/0.52  % (2025)Time elapsed: 0.100 s
% 0.22/0.52  % (2025)------------------------------
% 0.22/0.52  % (2025)------------------------------
% 0.22/0.52  % (2030)Refutation not found, incomplete strategy% (2030)------------------------------
% 0.22/0.52  % (2030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2030)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2030)Memory used [KB]: 10490
% 0.22/0.52  % (2030)Time elapsed: 0.099 s
% 0.22/0.52  % (2030)------------------------------
% 0.22/0.52  % (2030)------------------------------
% 0.22/0.52  % (2032)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (2032)Refutation not found, incomplete strategy% (2032)------------------------------
% 0.22/0.52  % (2032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2032)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2032)Memory used [KB]: 10490
% 0.22/0.52  % (2032)Time elapsed: 0.106 s
% 0.22/0.52  % (2032)------------------------------
% 0.22/0.52  % (2032)------------------------------
% 0.22/0.52  % (2035)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (2035)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f88,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    v4_relat_1(sK4,sK1)),
% 0.22/0.52    inference(resolution,[],[f52,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(sK0,X0) | v4_relat_1(sK4,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f50,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    v1_relat_1(sK4)),
% 0.22/0.52    inference(resolution,[],[f31,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(sK0,X0) | ~v1_relat_1(sK4) | v4_relat_1(sK4,X0)) )),
% 0.22/0.52    inference(resolution,[],[f49,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | v4_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(sK4),X0) | ~r1_tarski(sK0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f30,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    sK0 = k2_xboole_0(k1_relat_1(sK4),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f47,f38])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ~v1_relat_1(sK4) | sK0 = k2_xboole_0(k1_relat_1(sK4),sK0)),
% 0.22/0.52    inference(resolution,[],[f40,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    v4_relat_1(sK4,sK0)),
% 0.22/0.52    inference(resolution,[],[f32,f20])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~v4_relat_1(X2,X3) | ~v1_relat_1(X2) | k2_xboole_0(k1_relat_1(X2),X3) = X3) )),
% 0.22/0.52    inference(resolution,[],[f25,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ~v4_relat_1(sK4,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f85,f38])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ~v1_relat_1(sK4) | ~v4_relat_1(sK4,sK1)),
% 0.22/0.52    inference(resolution,[],[f84,f25])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK4),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f83,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    v5_relat_1(sK4,sK3)),
% 0.22/0.52    inference(resolution,[],[f66,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    r1_tarski(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(sK2,X0) | v5_relat_1(sK4,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f64,f38])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(sK2,X0) | ~v1_relat_1(sK4) | v5_relat_1(sK4,X0)) )),
% 0.22/0.52    inference(resolution,[],[f63,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | v5_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(sK4),X0) | ~r1_tarski(sK2,X0)) )),
% 0.22/0.52    inference(superposition,[],[f30,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    sK2 = k2_xboole_0(k2_relat_1(sK4),sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f61,f38])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ~v1_relat_1(sK4) | sK2 = k2_xboole_0(k2_relat_1(sK4),sK2)),
% 0.22/0.52    inference(resolution,[],[f43,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    v5_relat_1(sK4,sK2)),
% 0.22/0.52    inference(resolution,[],[f33,f20])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~v5_relat_1(X2,X3) | ~v1_relat_1(X2) | k2_xboole_0(k2_relat_1(X2),X3) = X3) )),
% 0.22/0.52    inference(resolution,[],[f27,f28])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK4),sK1) | ~v5_relat_1(sK4,sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f80,f38])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK4),sK1) | ~v1_relat_1(sK4) | ~v5_relat_1(sK4,sK3)),
% 0.22/0.52    inference(resolution,[],[f79,f27])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f75,f38])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK4),sK1) | ~r1_tarski(k2_relat_1(sK4),sK3) | ~v1_relat_1(sK4)),
% 0.22/0.52    inference(resolution,[],[f29,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (2035)------------------------------
% 0.22/0.52  % (2035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2035)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (2035)Memory used [KB]: 6140
% 0.22/0.52  % (2035)Time elapsed: 0.061 s
% 0.22/0.52  % (2035)------------------------------
% 0.22/0.52  % (2035)------------------------------
% 0.22/0.52  % (2021)Success in time 0.159 s
%------------------------------------------------------------------------------
