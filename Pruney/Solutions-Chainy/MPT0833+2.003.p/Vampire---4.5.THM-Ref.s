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
% DateTime   : Thu Dec  3 12:57:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  96 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 220 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(subsumption_resolution,[],[f91,f86])).

fof(f86,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f30,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

fof(f91,plain,(
    ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(forward_demodulation,[],[f90,f84])).

fof(f84,plain,(
    sK3 = k8_relat_1(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f61,f78,f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f78,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f77,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f77,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f56,f76,f43])).

% (21341)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f76,plain,(
    r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f74,f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f74,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f61,f70,f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f70,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f56,plain,(
    m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f53,f39])).

fof(f53,plain,(
    r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f31,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f90,plain,(
    ~ r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) ),
    inference(backward_demodulation,[],[f32,f89])).

fof(f89,plain,(
    ! [X0] : k6_relset_1(sK0,sK1,X0,sK3) = k8_relat_1(X0,sK3) ),
    inference(unit_resulting_resolution,[],[f30,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f32,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (21334)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.48  % (21339)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.48  % (21338)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.48  % (21355)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.48  % (21336)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.48  % (21337)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.48  % (21346)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (21347)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.48  % (21332)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.48  % (21357)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.49  % (21339)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (21333)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.49  % (21350)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.49  % (21345)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f30,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.49    inference(equality_resolution,[],[f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 0.22/0.49    inference(negated_conjecture,[],[f12])).
% 0.22/0.49  fof(f12,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.22/0.49    inference(forward_demodulation,[],[f90,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    sK3 = k8_relat_1(sK2,sK3)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f61,f78,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f77,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f56,f76,f43])).
% 0.22/0.49  % (21341)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f33,f74,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f71,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f61,f70,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    v5_relat_1(sK3,sK1)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f30,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f53,f39])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f31,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    r1_tarski(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    v1_relat_1(sK3)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f30,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)),
% 0.22/0.49    inference(backward_demodulation,[],[f32,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relset_1(sK0,sK1,X0,sK3) = k8_relat_1(X0,sK3)) )),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f30,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (21339)------------------------------
% 0.22/0.49  % (21339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21339)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (21339)Memory used [KB]: 1663
% 0.22/0.49  % (21339)Time elapsed: 0.085 s
% 0.22/0.49  % (21339)------------------------------
% 0.22/0.49  % (21339)------------------------------
% 0.22/0.49  % (21342)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.49  % (21331)Success in time 0.125 s
%------------------------------------------------------------------------------
