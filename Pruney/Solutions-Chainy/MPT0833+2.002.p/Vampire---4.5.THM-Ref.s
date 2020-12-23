%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:05 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   64 (  96 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :   19
%              Number of atoms          :  140 ( 223 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f81,f32])).

fof(f32,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

fof(f81,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f79,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

% (12511)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f79,plain,(
    ! [X0] : ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK2)) ),
    inference(resolution,[],[f77,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f77,plain,(
    ! [X0] : ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    inference(resolution,[],[f76,f31])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) ) ),
    inference(resolution,[],[f74,f34])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f74,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(X3)
      | ~ r1_tarski(X3,k1_zfmisc_1(k2_zfmisc_1(X4,sK2)))
      | ~ m1_subset_1(sK3,X3) ) ),
    inference(resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_tarski(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) ) ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f67,plain,(
    ! [X0] : ~ r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f64,plain,(
    ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    inference(resolution,[],[f61,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f61,plain,(
    ~ v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(sK3),X1)
      | ~ v5_relat_1(sK3,X1) ) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f52,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f60,plain,(
    ~ r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f59,f31])).

fof(f59,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f58,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X1,X2,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(condensation,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f58,plain,
    ( ~ r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(superposition,[],[f57,f55])).

fof(f55,plain,(
    ! [X2] :
      ( sK3 = k8_relat_1(X2,sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X2) ) ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f56,plain,
    ( ~ r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f33,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (833290240)
% 0.14/0.38  ipcrm: permission denied for id (833323015)
% 0.14/0.38  ipcrm: permission denied for id (833388556)
% 0.14/0.41  ipcrm: permission denied for id (833454112)
% 0.14/0.41  ipcrm: permission denied for id (833552418)
% 0.21/0.41  ipcrm: permission denied for id (833519653)
% 0.21/0.42  ipcrm: permission denied for id (833650731)
% 0.21/0.43  ipcrm: permission denied for id (833683505)
% 0.21/0.43  ipcrm: permission denied for id (833716274)
% 0.21/0.44  ipcrm: permission denied for id (833781817)
% 0.21/0.45  ipcrm: permission denied for id (833814593)
% 0.21/0.45  ipcrm: permission denied for id (833847362)
% 0.21/0.45  ipcrm: permission denied for id (833880131)
% 0.21/0.45  ipcrm: permission denied for id (833912901)
% 0.21/0.46  ipcrm: permission denied for id (833945675)
% 0.21/0.47  ipcrm: permission denied for id (833978447)
% 0.21/0.47  ipcrm: permission denied for id (834043987)
% 0.21/0.48  ipcrm: permission denied for id (834076759)
% 0.21/0.49  ipcrm: permission denied for id (834207840)
% 0.21/0.49  ipcrm: permission denied for id (834240610)
% 0.21/0.52  ipcrm: permission denied for id (834437242)
% 1.22/0.67  % (12506)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.67  % (12510)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.67  % (12513)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.68  % (12526)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.22/0.68  % (12505)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.68  % (12518)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.22/0.68  % (12526)Refutation found. Thanks to Tanya!
% 1.22/0.68  % SZS status Theorem for theBenchmark
% 1.22/0.68  % SZS output start Proof for theBenchmark
% 1.22/0.68  fof(f83,plain,(
% 1.22/0.68    $false),
% 1.22/0.68    inference(subsumption_resolution,[],[f81,f32])).
% 1.22/0.68  fof(f32,plain,(
% 1.22/0.68    r1_tarski(sK1,sK2)),
% 1.22/0.68    inference(cnf_transformation,[],[f16])).
% 1.22/0.68  fof(f16,plain,(
% 1.22/0.68    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.68    inference(flattening,[],[f15])).
% 1.22/0.68  fof(f15,plain,(
% 1.22/0.68    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.68    inference(ennf_transformation,[],[f14])).
% 1.22/0.68  fof(f14,negated_conjecture,(
% 1.22/0.68    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 1.22/0.68    inference(negated_conjecture,[],[f13])).
% 1.22/0.68  fof(f13,conjecture,(
% 1.22/0.68    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 1.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).
% 1.22/0.68  fof(f81,plain,(
% 1.22/0.68    ~r1_tarski(sK1,sK2)),
% 1.22/0.68    inference(resolution,[],[f79,f45])).
% 1.22/0.68  fof(f45,plain,(
% 1.22/0.68    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.22/0.68    inference(cnf_transformation,[],[f25])).
% 1.22/0.68  fof(f25,plain,(
% 1.22/0.68    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.22/0.68    inference(ennf_transformation,[],[f2])).
% 1.22/0.68  fof(f2,axiom,(
% 1.22/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.22/0.68  % (12511)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.68  fof(f79,plain,(
% 1.22/0.68    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK2))) )),
% 1.22/0.68    inference(resolution,[],[f77,f40])).
% 1.22/0.68  fof(f40,plain,(
% 1.22/0.68    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.22/0.68    inference(cnf_transformation,[],[f23])).
% 1.22/0.68  fof(f23,plain,(
% 1.22/0.68    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.22/0.68    inference(ennf_transformation,[],[f3])).
% 1.22/0.68  fof(f3,axiom,(
% 1.22/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.22/0.68  fof(f77,plain,(
% 1.22/0.68    ( ! [X0] : (~r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 1.22/0.68    inference(resolution,[],[f76,f31])).
% 1.22/0.68  fof(f31,plain,(
% 1.22/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.22/0.68    inference(cnf_transformation,[],[f16])).
% 1.22/0.69  fof(f76,plain,(
% 1.22/0.69    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))) )),
% 1.22/0.69    inference(resolution,[],[f74,f34])).
% 1.22/0.69  fof(f34,plain,(
% 1.22/0.69    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.22/0.69    inference(cnf_transformation,[],[f4])).
% 1.22/0.69  fof(f4,axiom,(
% 1.22/0.69    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.22/0.69  fof(f74,plain,(
% 1.22/0.69    ( ! [X4,X3] : (v1_xboole_0(X3) | ~r1_tarski(X3,k1_zfmisc_1(k2_zfmisc_1(X4,sK2))) | ~m1_subset_1(sK3,X3)) )),
% 1.22/0.69    inference(resolution,[],[f68,f39])).
% 1.22/0.69  fof(f39,plain,(
% 1.22/0.69    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f22])).
% 1.22/0.69  fof(f22,plain,(
% 1.22/0.69    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.22/0.69    inference(flattening,[],[f21])).
% 1.22/0.69  fof(f21,plain,(
% 1.22/0.69    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.22/0.69    inference(ennf_transformation,[],[f6])).
% 1.22/0.69  fof(f6,axiom,(
% 1.22/0.69    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.22/0.69  fof(f68,plain,(
% 1.22/0.69    ( ! [X0,X1] : (~r2_hidden(sK3,X0) | ~r1_tarski(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))) )),
% 1.22/0.69    inference(resolution,[],[f67,f41])).
% 1.22/0.69  fof(f41,plain,(
% 1.22/0.69    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f24])).
% 1.22/0.69  fof(f24,plain,(
% 1.22/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.22/0.69    inference(ennf_transformation,[],[f1])).
% 1.22/0.69  fof(f1,axiom,(
% 1.22/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.22/0.69  fof(f67,plain,(
% 1.22/0.69    ( ! [X0] : (~r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 1.22/0.69    inference(resolution,[],[f64,f38])).
% 1.22/0.69  fof(f38,plain,(
% 1.22/0.69    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f20])).
% 1.22/0.69  fof(f20,plain,(
% 1.22/0.69    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.22/0.69    inference(ennf_transformation,[],[f5])).
% 1.22/0.69  fof(f5,axiom,(
% 1.22/0.69    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.22/0.69  fof(f64,plain,(
% 1.22/0.69    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 1.22/0.69    inference(resolution,[],[f61,f48])).
% 1.22/0.69  fof(f48,plain,(
% 1.22/0.69    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/0.69    inference(cnf_transformation,[],[f27])).
% 1.22/0.69  fof(f27,plain,(
% 1.22/0.69    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.69    inference(ennf_transformation,[],[f10])).
% 1.22/0.69  fof(f10,axiom,(
% 1.22/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.22/0.69  fof(f61,plain,(
% 1.22/0.69    ~v5_relat_1(sK3,sK2)),
% 1.22/0.69    inference(resolution,[],[f60,f54])).
% 1.22/0.69  fof(f54,plain,(
% 1.22/0.69    ( ! [X1] : (r1_tarski(k2_relat_1(sK3),X1) | ~v5_relat_1(sK3,X1)) )),
% 1.22/0.69    inference(resolution,[],[f52,f37])).
% 1.22/0.69  fof(f37,plain,(
% 1.22/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f19])).
% 1.22/0.69  fof(f19,plain,(
% 1.22/0.69    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.22/0.69    inference(ennf_transformation,[],[f7])).
% 1.22/0.69  fof(f7,axiom,(
% 1.22/0.69    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.22/0.69  fof(f52,plain,(
% 1.22/0.69    v1_relat_1(sK3)),
% 1.22/0.69    inference(resolution,[],[f31,f46])).
% 1.22/0.69  fof(f46,plain,(
% 1.22/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f26])).
% 1.22/0.69  fof(f26,plain,(
% 1.22/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.69    inference(ennf_transformation,[],[f9])).
% 1.22/0.69  fof(f9,axiom,(
% 1.22/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.22/0.69  fof(f60,plain,(
% 1.22/0.69    ~r1_tarski(k2_relat_1(sK3),sK2)),
% 1.22/0.69    inference(subsumption_resolution,[],[f59,f31])).
% 1.22/0.69  fof(f59,plain,(
% 1.22/0.69    ~r1_tarski(k2_relat_1(sK3),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.22/0.69    inference(resolution,[],[f58,f51])).
% 1.22/0.69  fof(f51,plain,(
% 1.22/0.69    ( ! [X2,X0,X1] : (r2_relset_1(X1,X2,X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.22/0.69    inference(condensation,[],[f50])).
% 1.22/0.69  fof(f50,plain,(
% 1.22/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 1.22/0.69    inference(cnf_transformation,[],[f30])).
% 1.22/0.69  fof(f30,plain,(
% 1.22/0.69    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.69    inference(flattening,[],[f29])).
% 1.22/0.69  fof(f29,plain,(
% 1.22/0.69    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.22/0.69    inference(ennf_transformation,[],[f12])).
% 1.22/0.69  fof(f12,axiom,(
% 1.22/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.22/0.69  fof(f58,plain,(
% 1.22/0.69    ~r2_relset_1(sK0,sK1,sK3,sK3) | ~r1_tarski(k2_relat_1(sK3),sK2)),
% 1.22/0.69    inference(superposition,[],[f57,f55])).
% 1.22/0.69  fof(f55,plain,(
% 1.22/0.69    ( ! [X2] : (sK3 = k8_relat_1(X2,sK3) | ~r1_tarski(k2_relat_1(sK3),X2)) )),
% 1.22/0.69    inference(resolution,[],[f52,f35])).
% 1.22/0.69  fof(f35,plain,(
% 1.22/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 1.22/0.69    inference(cnf_transformation,[],[f18])).
% 1.22/0.69  fof(f18,plain,(
% 1.22/0.69    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.22/0.69    inference(flattening,[],[f17])).
% 1.22/0.69  fof(f17,plain,(
% 1.22/0.69    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.22/0.69    inference(ennf_transformation,[],[f8])).
% 1.22/0.69  fof(f8,axiom,(
% 1.22/0.69    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.22/0.69  fof(f57,plain,(
% 1.22/0.69    ~r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)),
% 1.22/0.69    inference(subsumption_resolution,[],[f56,f31])).
% 1.22/0.69  fof(f56,plain,(
% 1.22/0.69    ~r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.22/0.69    inference(superposition,[],[f33,f49])).
% 1.22/0.69  fof(f49,plain,(
% 1.22/0.69    ( ! [X2,X0,X3,X1] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/0.69    inference(cnf_transformation,[],[f28])).
% 1.22/0.69  fof(f28,plain,(
% 1.22/0.69    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.69    inference(ennf_transformation,[],[f11])).
% 1.22/0.69  fof(f11,axiom,(
% 1.22/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 1.22/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 1.22/0.69  fof(f33,plain,(
% 1.22/0.69    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 1.22/0.69    inference(cnf_transformation,[],[f16])).
% 1.22/0.69  % SZS output end Proof for theBenchmark
% 1.22/0.69  % (12526)------------------------------
% 1.22/0.69  % (12526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (12526)Termination reason: Refutation
% 1.22/0.69  
% 1.22/0.69  % (12526)Memory used [KB]: 1663
% 1.22/0.69  % (12507)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.69  % (12526)Time elapsed: 0.068 s
% 1.22/0.69  % (12526)------------------------------
% 1.22/0.69  % (12526)------------------------------
% 1.22/0.69  % (12349)Success in time 0.324 s
%------------------------------------------------------------------------------
