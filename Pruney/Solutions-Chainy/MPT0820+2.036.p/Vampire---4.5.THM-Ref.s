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
% DateTime   : Thu Dec  3 12:56:24 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   59 (  93 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 187 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f977,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f37,f974,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f974,plain,(
    ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f861,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f861,plain,(
    ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f74,f769,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f769,plain,(
    ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f735,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f735,plain,(
    ~ r1_tarski(k1_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f90,f31,f193])).

fof(f193,plain,(
    ! [X1] :
      ( r1_tarski(k3_relat_1(sK2),X1)
      | ~ r1_tarski(k2_relat_1(sK2),X1)
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(superposition,[],[f32,f66])).

fof(f66,plain,(
    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f56,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f42,f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f31,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK2),k2_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f70,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f70,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f56,f55,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f55,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f74,plain,(
    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f69,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f56,f54,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f54,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:00:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (29694)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (29693)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (29705)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.50  % (29693)Refutation not found, incomplete strategy% (29693)------------------------------
% 0.19/0.50  % (29693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (29705)Refutation not found, incomplete strategy% (29705)------------------------------
% 0.19/0.50  % (29705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (29705)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (29705)Memory used [KB]: 10746
% 0.19/0.50  % (29705)Time elapsed: 0.090 s
% 0.19/0.50  % (29705)------------------------------
% 0.19/0.50  % (29705)------------------------------
% 0.19/0.50  % (29686)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (29693)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (29693)Memory used [KB]: 10746
% 0.19/0.50  % (29693)Time elapsed: 0.095 s
% 0.19/0.50  % (29693)------------------------------
% 0.19/0.50  % (29693)------------------------------
% 0.19/0.51  % (29690)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (29700)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.51  % (29696)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (29699)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (29714)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (29707)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (29708)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (29707)Refutation not found, incomplete strategy% (29707)------------------------------
% 0.19/0.52  % (29707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (29707)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (29707)Memory used [KB]: 10746
% 0.19/0.52  % (29707)Time elapsed: 0.084 s
% 0.19/0.52  % (29707)------------------------------
% 0.19/0.52  % (29707)------------------------------
% 0.19/0.53  % (29685)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (29698)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (29689)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (29688)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (29691)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.53  % (29687)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.54  % (29687)Refutation not found, incomplete strategy% (29687)------------------------------
% 0.19/0.54  % (29687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (29687)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (29687)Memory used [KB]: 10746
% 0.19/0.54  % (29687)Time elapsed: 0.126 s
% 0.19/0.54  % (29687)------------------------------
% 0.19/0.54  % (29687)------------------------------
% 0.19/0.54  % (29695)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (29711)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.54  % (29706)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.54  % (29706)Refutation not found, incomplete strategy% (29706)------------------------------
% 0.19/0.54  % (29706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (29706)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (29706)Memory used [KB]: 1663
% 0.19/0.54  % (29706)Time elapsed: 0.138 s
% 0.19/0.54  % (29706)------------------------------
% 0.19/0.54  % (29706)------------------------------
% 1.45/0.54  % (29712)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.54  % (29692)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.54  % (29703)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.54  % (29697)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.54  % (29704)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.54  % (29709)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.55  % (29710)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.55  % (29701)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (29702)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.56  % (29713)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.61/0.57  % (29689)Refutation found. Thanks to Tanya!
% 1.61/0.57  % SZS status Theorem for theBenchmark
% 1.61/0.57  % SZS output start Proof for theBenchmark
% 1.61/0.57  fof(f977,plain,(
% 1.61/0.57    $false),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f37,f974,f36])).
% 1.61/0.57  fof(f36,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f22])).
% 1.61/0.57  fof(f22,plain,(
% 1.61/0.57    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f7])).
% 1.61/0.57  fof(f7,axiom,(
% 1.61/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.61/0.57  fof(f974,plain,(
% 1.61/0.57    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f861,f34])).
% 1.61/0.57  fof(f34,plain,(
% 1.61/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f8])).
% 1.61/0.57  fof(f8,axiom,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.61/0.57  fof(f861,plain,(
% 1.61/0.57    ~m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK0,sK1))))),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f74,f769,f51])).
% 1.61/0.57  fof(f51,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f29])).
% 1.61/0.57  fof(f29,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.61/0.57    inference(flattening,[],[f28])).
% 1.61/0.57  fof(f28,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.61/0.57    inference(ennf_transformation,[],[f9])).
% 1.61/0.57  fof(f9,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.61/0.57  fof(f769,plain,(
% 1.61/0.57    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f735,f35])).
% 1.61/0.57  fof(f35,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f8])).
% 1.61/0.57  fof(f735,plain,(
% 1.61/0.57    ~r1_tarski(k1_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f90,f31,f193])).
% 1.61/0.57  fof(f193,plain,(
% 1.61/0.57    ( ! [X1] : (r1_tarski(k3_relat_1(sK2),X1) | ~r1_tarski(k2_relat_1(sK2),X1) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 1.61/0.57    inference(superposition,[],[f32,f66])).
% 1.61/0.57  fof(f66,plain,(
% 1.61/0.57    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f56,f38])).
% 1.61/0.57  fof(f38,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f23])).
% 1.61/0.57  fof(f23,plain,(
% 1.61/0.57    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f13])).
% 1.61/0.57  fof(f13,axiom,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.61/0.57  fof(f56,plain,(
% 1.61/0.57    v1_relat_1(sK2)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f42,f30,f39])).
% 1.61/0.57  fof(f39,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f24])).
% 1.61/0.57  fof(f24,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f10])).
% 1.61/0.57  fof(f10,axiom,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.61/0.57  fof(f30,plain,(
% 1.61/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.61/0.57    inference(cnf_transformation,[],[f18])).
% 1.61/0.57  fof(f18,plain,(
% 1.61/0.57    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(ennf_transformation,[],[f17])).
% 1.61/0.57  fof(f17,negated_conjecture,(
% 1.61/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 1.61/0.57    inference(negated_conjecture,[],[f16])).
% 1.61/0.57  fof(f16,conjecture,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 1.61/0.57  fof(f42,plain,(
% 1.61/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f14])).
% 1.61/0.57  fof(f14,axiom,(
% 1.61/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.61/0.57  fof(f32,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f20])).
% 1.61/0.57  fof(f20,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.61/0.57    inference(flattening,[],[f19])).
% 1.61/0.57  fof(f19,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.61/0.57    inference(ennf_transformation,[],[f3])).
% 1.61/0.57  fof(f3,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.61/0.57  fof(f31,plain,(
% 1.61/0.57    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 1.61/0.57    inference(cnf_transformation,[],[f18])).
% 1.61/0.57  fof(f90,plain,(
% 1.61/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),k2_xboole_0(X0,sK1))) )),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f70,f33])).
% 1.61/0.57  fof(f33,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f21])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.61/0.57  fof(f70,plain,(
% 1.61/0.57    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f56,f55,f48])).
% 1.61/0.57  fof(f48,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f26,plain,(
% 1.61/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f12])).
% 1.61/0.57  fof(f12,axiom,(
% 1.61/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.61/0.57  fof(f55,plain,(
% 1.61/0.57    v5_relat_1(sK2,sK1)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f30,f41])).
% 1.61/0.57  fof(f41,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f25])).
% 1.61/0.57  fof(f25,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(ennf_transformation,[],[f15])).
% 1.61/0.57  fof(f15,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.61/0.57  fof(f74,plain,(
% 1.61/0.57    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f69,f53])).
% 1.61/0.57  fof(f53,plain,(
% 1.61/0.57    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.61/0.57    inference(equality_resolution,[],[f43])).
% 1.61/0.57  fof(f43,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.61/0.57    inference(cnf_transformation,[],[f5])).
% 1.61/0.57  fof(f5,axiom,(
% 1.61/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.61/0.57  fof(f69,plain,(
% 1.61/0.57    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f56,f54,f50])).
% 1.61/0.59  fof(f50,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f27])).
% 1.61/0.59  fof(f27,plain,(
% 1.61/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f11])).
% 1.61/0.59  fof(f11,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.61/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.61/0.59  fof(f54,plain,(
% 1.61/0.59    v4_relat_1(sK2,sK0)),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f30,f40])).
% 1.61/0.59  fof(f40,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f25])).
% 1.61/0.59  fof(f37,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f2])).
% 1.61/0.59  fof(f2,axiom,(
% 1.61/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.61/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.61/0.59  % SZS output end Proof for theBenchmark
% 1.61/0.59  % (29689)------------------------------
% 1.61/0.59  % (29689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (29689)Termination reason: Refutation
% 1.61/0.59  
% 1.61/0.59  % (29689)Memory used [KB]: 6908
% 1.61/0.59  % (29689)Time elapsed: 0.171 s
% 1.61/0.59  % (29689)------------------------------
% 1.61/0.59  % (29689)------------------------------
% 1.61/0.59  % (29684)Success in time 0.23 s
%------------------------------------------------------------------------------
