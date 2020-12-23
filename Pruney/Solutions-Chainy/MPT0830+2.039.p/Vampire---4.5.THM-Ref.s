%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 116 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 251 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(subsumption_resolution,[],[f69,f35])).

fof(f35,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f34,f24])).

fof(f24,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f34,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f69,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f68,f39])).

fof(f39,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f30,f21])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f68,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f67,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

fof(f67,plain,(
    ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    inference(subsumption_resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f40,f35])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f31,f39])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | v1_relat_1(k7_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    inference(resolution,[],[f65,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f65,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f63,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f63,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f62,f41])).

fof(f62,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f28,f53])).

fof(f53,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f22,f52])).

fof(f52,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK0,sK2,sK3,X0) ),
    inference(resolution,[],[f33,f21])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f22,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (9713)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.48  % (9709)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.48  % (9728)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.48  % (9730)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.49  % (9716)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (9712)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (9721)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (9711)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (9733)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (9725)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (9714)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (9733)Refutation not found, incomplete strategy% (9733)------------------------------
% 0.20/0.49  % (9733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9710)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (9717)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (9733)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9733)Memory used [KB]: 10618
% 0.20/0.50  % (9733)Time elapsed: 0.052 s
% 0.20/0.50  % (9733)------------------------------
% 0.20/0.50  % (9733)------------------------------
% 0.20/0.50  % (9720)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.50  % (9722)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (9716)Refutation not found, incomplete strategy% (9716)------------------------------
% 0.20/0.50  % (9716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9716)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9716)Memory used [KB]: 10618
% 0.20/0.50  % (9716)Time elapsed: 0.085 s
% 0.20/0.50  % (9716)------------------------------
% 0.20/0.50  % (9716)------------------------------
% 0.20/0.50  % (9723)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (9719)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (9712)Refutation not found, incomplete strategy% (9712)------------------------------
% 0.20/0.50  % (9712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9712)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9712)Memory used [KB]: 10490
% 0.20/0.50  % (9712)Time elapsed: 0.084 s
% 0.20/0.50  % (9712)------------------------------
% 0.20/0.50  % (9712)------------------------------
% 0.20/0.50  % (9717)Refutation not found, incomplete strategy% (9717)------------------------------
% 0.20/0.50  % (9717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9717)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9717)Memory used [KB]: 6012
% 0.20/0.50  % (9717)Time elapsed: 0.092 s
% 0.20/0.50  % (9717)------------------------------
% 0.20/0.50  % (9717)------------------------------
% 0.20/0.50  % (9730)Refutation not found, incomplete strategy% (9730)------------------------------
% 0.20/0.50  % (9730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9730)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9730)Memory used [KB]: 6140
% 0.20/0.50  % (9730)Time elapsed: 0.092 s
% 0.20/0.50  % (9730)------------------------------
% 0.20/0.50  % (9730)------------------------------
% 0.20/0.50  % (9732)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (9729)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (9723)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f69,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    v1_relat_1(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f34,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f23,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ~v1_relat_1(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f68,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    v5_relat_1(sK3,sK2)),
% 0.20/0.50    inference(resolution,[],[f30,f21])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ~v5_relat_1(sK3,sK2) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f67,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v5_relat_1(k7_relat_1(X2,X0),X1) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ~v5_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f66,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f40,f35])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(sK3) | v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.20/0.50    inference(resolution,[],[f31,f39])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v5_relat_1(X2,X1) | ~v1_relat_1(X2) | v1_relat_1(k7_relat_1(X2,X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v5_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 0.20/0.50    inference(resolution,[],[f65,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f64,f35])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f63,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f62,f41])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.20/0.50    inference(resolution,[],[f28,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    inference(backward_demodulation,[],[f22,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK0,sK2,sK3,X0)) )),
% 0.20/0.50    inference(resolution,[],[f33,f21])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (9723)------------------------------
% 0.20/0.50  % (9723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9723)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (9723)Memory used [KB]: 6140
% 0.20/0.50  % (9723)Time elapsed: 0.103 s
% 0.20/0.50  % (9723)------------------------------
% 0.20/0.50  % (9723)------------------------------
% 0.20/0.50  % (9706)Success in time 0.147 s
%------------------------------------------------------------------------------
